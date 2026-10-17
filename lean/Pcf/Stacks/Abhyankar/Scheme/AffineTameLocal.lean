/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.Scheme.Defs
public import Pcf.Stacks.Abhyankar.Scheme.IntegralClosureAway
public import Pcf.Stacks.Abhyankar.Tag0EYE
public import Pcf.Stacks.Abhyankar.StrictRootComponent
public import Mathlib.RingTheory.Localization.AtPrime.Extension

/-!
# The chart at a point of the divisor: localizing at `y`

Setting: `R` Noetherian, `a ∈ R` a nonzerodivisor with `R/(a)` regular, `B` finite étale over
`R_a`, `y ∈ V(a)`.  This file prepares the application of the affine hypothesis
`AbhyankarLemmaTameOfFinite` at the local ring `R_y`:

* `By B y = R_y ⊗_R B` and `Ny B y`, the integral closure of `R_y` in `B_y`;
* `isLocalization_away_ny`, `isIntegralClosure_ny`: `B_y = N_y[1/a]` and `N_y` is the integral
  closure of `R_y` in `N_y[1/a]`;
* `isEtaleAt_ny`: `N_y` is étale over `R_y` at primes not containing `a`;
* `finite_ny`: `N_y` is finite over `R_y` when `R_y` is a Noetherian normal domain
  (`finite_integralClosure_of_etale_fractionRing`: the integral closure of a Noetherian normal
  domain in a finite étale algebra over its fraction field is finite);
* `isTamelyRamifiedAt_of_isLocalization`: tameness at a prime of `S` over `p` may be checked
  after localizing at `p` (Mathlib's localization invariance of `Ideal.ramificationIdx` plus the
  residue-field comparison along a map that is surjective on stalks).

## Relation to the Stacks proof of Tag `0EYG`

Stacks reduces to the strict henselization and works with `B` itself.  Here the affine
hypothesis (`Pcf.Stacks.AbhyankarLemmaTameOfFinite`) is stated, like the characteristic-zero
`Pcf.Stacks.AbhyankarLemmaOfFinite`, for the
*normalization* `S` of `R` in `S[1/a]` and requires `S` finite.  The normalization of `R` in `B`
need not be known to be finite a priori, so the route differs from Stacks: we apply the hypothesis
at the regular local ring `R_y`, where finiteness of the normalization is the classical fact
that the integral closure of a Noetherian normal domain in a finite separable extension is finite
(Stacks Tag `032L`), and descend afterwards (see `AffineTame.lean`).  The finiteness of `S` over
`R` itself is a consequence (`Pcf.Stacks.finite_of_isIntegralClosure_away`).
-/

@[expose] public section

universe u

open TensorProduct IsLocalRing Algebra

set_option linter.style.haveILetI false

namespace Pcf.Stacks.SchemeLevel.AffineTame
section Chart

variable {R : Type u} [CommRing R] (a : R) (Ra : Type u) [CommRing Ra] [Algebra R Ra]
  [IsLocalization.Away a Ra]
  (B : Type u) [CommRing B] [Algebra Ra B] [Algebra R B] [IsScalarTower R Ra B]
  (y : Ideal R) [y.IsPrime]

/-- `B_y = R_y ⊗_R B`, as a type with its own instances (this avoids instance-path problems
for localizations of subalgebras of a tensor product). -/
def By : Type u := Localization.AtPrime y ⊗[R] B

noncomputable instance : CommRing (By B y) := Algebra.TensorProduct.instCommRing

noncomputable instance : Algebra (Localization.AtPrime y) (By B y) :=
  Algebra.TensorProduct.leftAlgebra

noncomputable instance : Algebra R (By B y) := Algebra.TensorProduct.leftAlgebra

instance : IsScalarTower R (Localization.AtPrime y) (By B y) :=
  inferInstanceAs (IsScalarTower R (Localization.AtPrime y) (Localization.AtPrime y ⊗[R] B))

/-- The inclusion `B → B_y`. -/
noncomputable def inclB : B →+* By B y :=
  (Algebra.TensorProduct.includeRight (R := R) (A := Localization.AtPrime y) (B := B)).toRingHom

/-- The algebra structure `R_y ⊗ R_a → B_y`. -/
noncomputable instance tensorAlgebra :
    Algebra (Localization.AtPrime y ⊗[R] Ra) (By B y) :=
  (Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime y) (Localization.AtPrime y))
    (IsScalarTower.toAlgHom R Ra B)).toRingHom.toAlgebra

/-- `R_y ⊗_R R_a` is the localization of `R_y` away from the image of `a`. -/
theorem isLocalization_tensor :
    IsLocalization.Away (algebraMap R (Localization.AtPrime y) a)
      (Localization.AtPrime y ⊗[R] Ra) := by
  have h := IsLocalization.tensor (S := Localization.AtPrime y) Ra (Submonoid.powers a)
  rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers] at h

instance : IsScalarTower (Localization.AtPrime y) (Localization.AtPrime y ⊗[R] Ra) (By B y) :=
  IsScalarTower.of_algebraMap_eq (R := Localization.AtPrime y)
    (S := Localization.AtPrime y ⊗[R] Ra) (A := By B y) fun r ↦ by
    change _ = Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime y) _)
      (IsScalarTower.toAlgHom R Ra B) (r ⊗ₜ 1)
    simp
    rfl

/-- The algebra map `R_y ⊗_R R_a → B_y` on pure tensors: `r ⊗ x ↦ r ⊗ x`. -/
theorem algebraMap_tensor_tmul (r : Localization.AtPrime y) (x : Ra) :
    algebraMap (Localization.AtPrime y ⊗[R] Ra) (By B y) (r ⊗ₜ x) =
      (show By B y from r ⊗ₜ[R] algebraMap Ra B x) := by
  change Algebra.TensorProduct.map _ _ (r ⊗ₜ x) = _
  simp

/-- If `B` is integral over `R_a`, then `B_y` is integral over `R_y ⊗_R R_a`. -/
theorem isIntegral_tensor [Algebra.IsIntegral Ra B] :
    Algebra.IsIntegral (Localization.AtPrime y ⊗[R] Ra) (By B y) := by
  constructor
  intro x
  change Localization.AtPrime y ⊗[R] B at x
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => exact hx.add hz
  | tmul r b =>
    have h1 : IsIntegral (Localization.AtPrime y ⊗[R] Ra)
        (algebraMap (Localization.AtPrime y ⊗[R] Ra) (By B y) (r ⊗ₜ 1)) :=
      isIntegral_algebraMap
    have h2 : IsIntegral (Localization.AtPrime y ⊗[R] Ra) (inclB B y b) := by
      have hb : IsIntegral Ra b := Algebra.IsIntegral.isIntegral b
      refine IsIntegral.map_of_comp_eq
        (Algebra.TensorProduct.includeRight (R := R) (A := Localization.AtPrime y)
          (B := Ra)).toRingHom
        (inclB B y) ?_ hb
      ext x
      exact algebraMap_tensor_tmul Ra B y 1 x
    have := h1.mul h2
    rw [algebraMap_tensor_tmul] at this
    change IsIntegral _ ((show By B y from r ⊗ₜ[R] algebraMap Ra B 1) *
      (show By B y from (1 : Localization.AtPrime y) ⊗ₜ[R] b)) at this
    rw [map_one] at this
    have e : (show By B y from r ⊗ₜ[R] (1 : B)) *
        (show By B y from (1 : Localization.AtPrime y) ⊗ₜ[R] b) =
        (show By B y from r ⊗ₜ[R] b) := by
      change (r ⊗ₜ[R] (1 : B)) * ((1 : Localization.AtPrime y) ⊗ₜ[R] b) = r ⊗ₜ[R] b
      simp
    rw [e] at this
    exact this

/-- Finiteness of an integral closure in a finite étale algebra over the fraction field. -/
theorem finite_integralClosure_of_etale_fractionRing
    (A : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    (L : Type u) [CommRing L] [Algebra (FractionRing A) L] [Algebra A L]
    [IsScalarTower A (FractionRing A) L]
    [Algebra.Etale (FractionRing A) L] [Module.Finite (FractionRing A) L] :
    Module.Finite A (integralClosure A L) := by
  classical
  obtain ⟨I, hI, Ai, _, _, e, hAi⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (FractionRing A) L).mp inferInstance
  letI := Fintype.ofFinite I
  letI (i : I) : Algebra A (Ai i) :=
    ((algebraMap (FractionRing A) (Ai i)).comp (algebraMap A (FractionRing A))).toAlgebra
  haveI (i : I) : IsScalarTower A (FractionRing A) (Ai i) := IsScalarTower.of_algebraMap_eq' rfl
  haveI (i : I) : Module.Finite (FractionRing A) (Ai i) := (hAi i).1
  haveI (i : I) : Algebra.IsSeparable (FractionRing A) (Ai i) := (hAi i).2
  haveI (i : I) : Module.Finite A (integralClosure A (Ai i)) :=
    IsIntegralClosure.finite A (FractionRing A) (Ai i) (integralClosure A (Ai i))
  let f : integralClosure A L →ₗ[A] (∀ i, integralClosure A (Ai i)) :=
    { toFun := fun x i ↦ ⟨e x.1 i, by
        have hx : IsIntegral A (e x.1) :=
          (x.2.map ((e.toAlgHom.restrictScalars A)))
        exact hx.map (Pi.evalAlgHom A Ai i)⟩
      map_add' := fun x y ↦ by ext i; simp
      map_smul' := fun r x ↦ by
        ext i
        simp only [SetLike.val_smul, RingHom.id_apply, Pi.smul_apply]
        rw [Algebra.smul_def, map_mul, Algebra.smul_def]
        rw [IsScalarTower.algebraMap_apply A (FractionRing A) L, AlgEquiv.commutes]
        rfl }
  refine Module.Finite.of_injective f ?_
  intro x y hxy
  apply Subtype.ext
  apply e.injective
  funext i
  have := congrFun hxy i
  exact congrArg Subtype.val this

variable [Module.Finite Ra B] [Algebra.Etale Ra B]

/-- The integral closure `N_y` of `R_y` in `B_y = R_y ⊗_R B`. -/
abbrev Ny : Type u := integralClosure (Localization.AtPrime y) (By B y)

/-- The image `a_y` of `a` in `R_y`. -/
abbrev ay : Localization.AtPrime y := algebraMap R (Localization.AtPrime y) a

omit [Algebra.Etale Ra B] in
include Ra in
/-- `B_y` is the localization of the normalization `N_y` away from `a_y`. -/
theorem isLocalization_away_ny :
    IsLocalization.Away (algebraMap (Localization.AtPrime y) (Ny B y) (ay a y))
      (By B y) := by
  have := isIntegral_tensor Ra B y
  have := isLocalization_tensor a Ra y
  exact isLocalization_away_integralClosure (ay a y)
    (Localization.AtPrime y ⊗[R] Ra) (By B y)

omit [Algebra.Etale Ra B] in
include Ra in
/-- `N_y` is the integral closure of `R_y` in `N_y[1/a_y]`. -/
theorem isIntegralClosure_ny :
    IsIntegralClosure (Ny B y) (Localization.AtPrime y)
      (Localization.Away (algebraMap (Localization.AtPrime y) (Ny B y) (ay a y))) := by
  have := isIntegral_tensor Ra B y
  have := isLocalization_tensor a Ra y
  exact isIntegralClosure_localizationAway_integralClosure (ay a y)
    (Localization.AtPrime y ⊗[R] Ra) (By B y)

omit [Module.Finite Ra B] in
include a Ra in
/-- `B_y = R_y ⊗_R B` is étale over `R_y` (as `B` is étale over `R_a`, hence over `R`). -/
theorem etale_by : Algebra.Etale (Localization.AtPrime y) (By B y) := by
  have : Algebra.Etale R Ra := Algebra.Etale.of_isLocalizationAway a
  have : Algebra.Etale R B := Algebra.Etale.comp R Ra B
  exact (inferInstance : Algebra.Etale (Localization.AtPrime y) (Localization.AtPrime y ⊗[R] B))

include Ra in
/-- `N_y` is étale over `R_y` at every prime not containing `a_y`. -/
theorem isEtaleAt_ny (w : PrimeSpectrum (Ny B y))
    (hw : algebraMap (Localization.AtPrime y) (Ny B y) (ay a y) ∉ w.asIdeal) :
    Algebra.IsEtaleAt (Localization.AtPrime y) w.asIdeal := by
  have := isLocalization_away_ny a Ra B y
  have := etale_by a Ra B y
  exact Pcf.Stacks.isEtaleAt_of_isLocalization_away (D := By B y) _ w hw

include a Ra in
/-- `N_y` is finite over `R_y` when `R_y` is a Noetherian normal domain (it will be regular local):
`B_y` embeds in the finite étale `K`-algebra `K ⊗ B_y`, whose integral closure over `R_y` is finite
(finite separable field extensions of the fraction field of a Noetherian normal domain). -/
theorem finite_ny [IsDomain (Localization.AtPrime y)] [IsIntegrallyClosed (Localization.AtPrime y)]
    [IsNoetherianRing (Localization.AtPrime y)] (ha : ay a y ≠ 0) :
    Module.Finite (Localization.AtPrime y) (Ny B y) := by
  let Ry := Localization.AtPrime y
  let K := FractionRing Ry
  let L := K ⊗[Ry] By B y
  have := etale_by a Ra B y
  have := isLocalization_tensor a Ra y
  have := isIntegral_tensor Ra B y
  have haK : IsUnit (algebraMap Ry K (ay a y)) :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero ha)).isUnit
  let φ : Localization.AtPrime y ⊗[R] Ra →+* K := IsLocalization.Away.lift (ay a y) haK
  let ψ : By B y →+* L := (Algebra.TensorProduct.includeRight (R := Ry) (A := K)).toRingHom
  have hcomp : (algebraMap K L).comp φ =
      ψ.comp (algebraMap (Localization.AtPrime y ⊗[R] Ra) (By B y)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (ay a y))
    ext r
    simp only [RingHom.comp_apply, φ, IsLocalization.Away.lift, IsLocalization.lift_eq, ψ]
    rw [← IsScalarTower.algebraMap_apply Ry (Localization.AtPrime y ⊗[R] Ra) (By B y)]
    change algebraMap K L (algebraMap Ry K r) =
      (Algebra.TensorProduct.includeRight (R := Ry) (A := K) (B := By B y))
        (algebraMap Ry (By B y) r)
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  have hint : Algebra.IsIntegral K L := by
    constructor
    intro x
    induction x using TensorProduct.inductionOn with
    | add x z hx hz => exact hx.add hz
    | tmul k b =>
      have h2 : IsIntegral K (ψ b) :=
        IsIntegral.map_of_comp_eq φ ψ hcomp (Algebra.IsIntegral.isIntegral b)
      have e : k ⊗ₜ[Ry] b = k • ((1 : K) ⊗ₜ[Ry] b) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e]
      exact h2.smul k
  have : Module.Finite K L := Algebra.IsIntegral.finite
  have hfin : Module.Finite Ry (integralClosure Ry L) :=
    finite_integralClosure_of_etale_fractionRing Ry L
  have hflat : Module.Flat Ry (By B y) := Algebra.Smooth.flat Ry (By B y)
  have hψinj : Function.Injective ψ := by
    have hK : Function.Injective (Algebra.linearMap Ry K) := IsFractionRing.injective Ry K
    have h := Module.Flat.rTensor_preserves_injective_linearMap (M := By B y) _ hK
    intro x z hxz
    apply (TensorProduct.lid Ry (By B y)).symm.injective
    apply h
    simpa [ψ] using hxz
  let f : Ny B y →ₗ[Ry] integralClosure Ry L :=
    { toFun := fun x ↦ ⟨ψ x.1, by
        have := x.2.map (Algebra.TensorProduct.includeRight (R := Ry) (A := K) (B := By B y))
        exact this⟩
      map_add' := fun x z ↦ by ext; simp
      map_smul' := fun r x ↦ by
        ext
        simp only [SetLike.val_smul, RingHom.id_apply]
        exact (Algebra.TensorProduct.includeRight (R := Ry) (A := K)
          (B := By B y)).toLinearMap.map_smul r x.1 }
  have : IsNoetherian Ry (integralClosure Ry L) := by
    have := isNoetherian_of_isNoetherianRing_of_finite (Localization.AtPrime y)
      (integralClosure Ry L)
    exact this
  refine Module.Finite.of_injective f ?_
  intro x z hxz
  apply Subtype.ext
  apply hψinj
  exact congrArg Subtype.val hxz

end Chart

section TameLocalization

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
  (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]
  (Sₚ : Type*) [CommRing Sₚ] [Algebra S Sₚ]
  [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ]
  [Algebra Rₚ Sₚ] [Algebra R Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ]

/-- For a prime `q` of `S` over `p`, the image of `R ∖ p` in `S` is disjoint from `q`. -/
theorem disjoint_primeCompl (q : Ideal S) [q.IsPrime] (hq : q.under R = p) :
    Disjoint (algebraMapSubmonoid S p.primeCompl : Set S) q := by
  rw [Set.disjoint_left]
  rintro _ ⟨r, hr, rfl⟩ hrq
  apply hr
  rw [← hq]
  exact hrq

omit [Algebra R Sₚ] [IsScalarTower R S Sₚ] in
/-- A prime `q` of `S` over `p` extends to a prime of the localization `S_p`. -/
theorem isPrime_map (q : Ideal S) [q.IsPrime] (hq : q.under R = p) :
    (q.map (algebraMap S Sₚ)).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint _ Sₚ q inferInstance (disjoint_primeCompl p q hq)

omit [Algebra R Sₚ] [IsScalarTower R S Sₚ] in
/-- A prime `q` of `S` over `p` is recovered from its extension to `S_p`. -/
theorem comap_map (q : Ideal S) [q.IsPrime] (hq : q.under R = p) :
    (q.map (algebraMap S Sₚ)).comap (algebraMap S Sₚ) = q :=
  IsLocalization.under_map_of_isPrime_disjoint _ Sₚ inferInstance (disjoint_primeCompl p q hq)

/-- Tameness at a prime `q` of `S` over `p` can be read after localizing at `p`. -/
theorem isTamelyRamifiedAt_of_isLocalization (q : PrimeSpectrum S) (hq : q.asIdeal.under R = p)
    (h : IsTamelyRamifiedAt Rₚ Sₚ
      ⟨q.asIdeal.map (algebraMap S Sₚ), isPrime_map p Sₚ q.asIdeal hq⟩) :
    IsTamelyRamifiedAt R S q := by
  haveI : q.asIdeal.LiesOver p := ⟨hq.symm⟩
  set m : Ideal Sₚ := q.asIdeal.map (algebraMap S Sₚ) with hm
  haveI : m.IsPrime := isPrime_map p Sₚ q.asIdeal hq
  have hidx : m.ramificationIdx Rₚ = q.asIdeal.ramificationIdx R :=
    IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx p Rₚ Sₚ q.asIdeal
  obtain ⟨h1, h2⟩ := h
  have hmq : q.asIdeal = m.comap (algebraMap S Sₚ) := (comap_map p Sₚ q.asIdeal hq).symm
  have hP0 : q.asIdeal.under R = (m.under Rₚ).comap (algebraMap R Rₚ) := by
    change q.asIdeal.comap (algebraMap R S) =
      (m.comap (algebraMap Rₚ Sₚ)).comap (algebraMap R Rₚ)
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R S Sₚ,
      ← Ideal.comap_comap, ← hmq]
  let e₁ := Ideal.ResidueField.map (q.asIdeal.under R) (m.under Rₚ) (algebraMap R Rₚ) hP0
  let e₂ := Ideal.ResidueField.map q.asIdeal m (algebraMap S Sₚ) hmq
  have hb₁ : Function.Bijective e₁ :=
    (RingHom.surjectiveOnStalks_of_isLocalization p.primeCompl Rₚ).residueFieldMap_bijective
      _ _ hP0
  have hb₂ : Function.Bijective e₂ :=
    (RingHom.surjectiveOnStalks_of_isLocalization (algebraMapSubmonoid S p.primeCompl)
      Sₚ).residueFieldMap_bijective _ _ hmq
  refine ⟨?_, ?_⟩
  · rw [isUnit_iff_ne_zero] at h1 ⊢
    intro hz
    apply h1
    rw [hidx]
    have := congrArg e₁ hz
    simpa using this
  · letI : Algebra (Localization.AtPrime (m.under Rₚ)) (Localization.AtPrime m) :=
      Localization.AtPrime.algebraOfLiesOver _ _
    letI : Algebra (Localization.AtPrime (q.asIdeal.under R)) (Localization.AtPrime q.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver _ _
    refine Algebra.IsSeparable.of_equiv_equiv (RingEquiv.ofBijective e₁ hb₁).symm
      (RingEquiv.ofBijective e₂ hb₂).symm ?_
    have key : e₂.comp (algebraMap (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) =
        (algebraMap (m.under Rₚ).ResidueField m.ResidueField).comp e₁ := by
      apply Ideal.ResidueField.ringHom_ext
      ext r
      simp only [RingHom.comp_apply]
      have hA : ∀ x, algebraMap (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField x =
          Ideal.ResidueField.map (q.asIdeal.under R) q.asIdeal (algebraMap R S) rfl x :=
        fun _ ↦ rfl
      have hB : ∀ x, algebraMap (m.under Rₚ).ResidueField m.ResidueField x =
          Ideal.ResidueField.map (m.under Rₚ) m (algebraMap Rₚ Sₚ) rfl x :=
        fun _ ↦ rfl
      rw [hA, hB]
      simp only [e₁, e₂, Ideal.ResidueField.map_algebraMap]
      rw [← IsScalarTower.algebraMap_apply R Rₚ Sₚ,
        ← IsScalarTower.algebraMap_apply R Sₚ m.ResidueField]
      rw [← IsScalarTower.algebraMap_apply R S Sₚ,
        ← IsScalarTower.algebraMap_apply R Sₚ m.ResidueField]
    refine RingHom.ext fun x ↦ ?_
    obtain ⟨x, rfl⟩ := hb₁.2 x
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    have h₁ : (RingEquiv.ofBijective e₁ hb₁).symm (e₁ x) = x :=
      (RingEquiv.ofBijective e₁ hb₁).symm_apply_apply x
    rw [h₁]
    apply hb₂.1
    have h₂ : e₂ ((RingEquiv.ofBijective e₂ hb₂).symm
        (algebraMap (m.under Rₚ).ResidueField m.ResidueField (e₁ x))) =
        algebraMap (m.under Rₚ).ResidueField m.ResidueField (e₁ x) :=
      (RingEquiv.ofBijective e₂ hb₂).apply_symm_apply _
    rw [h₂]
    exact (congrArg (fun f ↦ f x) key)

/-- Conversely, tameness at a prime `q` of `S` over `p` gives tameness at `q S_p` (the same
residue-field comparison and Mathlib's localization invariance of ramification indices). -/
theorem isTamelyRamifiedAt_map_of_isLocalization (q : PrimeSpectrum S)
    (hq : q.asIdeal.under R = p) (h : IsTamelyRamifiedAt R S q) :
    IsTamelyRamifiedAt Rₚ Sₚ ⟨q.asIdeal.map (algebraMap S Sₚ), isPrime_map p Sₚ q.asIdeal hq⟩ := by
  haveI : q.asIdeal.LiesOver p := ⟨hq.symm⟩
  set m : Ideal Sₚ := q.asIdeal.map (algebraMap S Sₚ) with hm
  haveI : m.IsPrime := isPrime_map p Sₚ q.asIdeal hq
  have hidx : m.ramificationIdx Rₚ = q.asIdeal.ramificationIdx R :=
    IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx p Rₚ Sₚ q.asIdeal
  obtain ⟨h1, h2⟩ := h
  have hmq : q.asIdeal = m.comap (algebraMap S Sₚ) := (comap_map p Sₚ q.asIdeal hq).symm
  have hP0 : q.asIdeal.under R = (m.under Rₚ).comap (algebraMap R Rₚ) := by
    change q.asIdeal.comap (algebraMap R S) =
      (m.comap (algebraMap Rₚ Sₚ)).comap (algebraMap R Rₚ)
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R S Sₚ,
      ← Ideal.comap_comap, ← hmq]
  let e₁ := Ideal.ResidueField.map (q.asIdeal.under R) (m.under Rₚ) (algebraMap R Rₚ) hP0
  let e₂ := Ideal.ResidueField.map q.asIdeal m (algebraMap S Sₚ) hmq
  have hb₁ : Function.Bijective e₁ :=
    (RingHom.surjectiveOnStalks_of_isLocalization p.primeCompl Rₚ).residueFieldMap_bijective
      _ _ hP0
  have hb₂ : Function.Bijective e₂ :=
    (RingHom.surjectiveOnStalks_of_isLocalization (algebraMapSubmonoid S p.primeCompl)
      Sₚ).residueFieldMap_bijective _ _ hmq
  refine ⟨?_, ?_⟩
  · change IsUnit ((m.ramificationIdx Rₚ : ℕ) : (m.under Rₚ).ResidueField)
    rw [hidx]
    simpa using h1.map e₁
  · letI : Algebra (Localization.AtPrime (m.under Rₚ)) (Localization.AtPrime m) :=
      Localization.AtPrime.algebraOfLiesOver _ _
    letI : Algebra (Localization.AtPrime (q.asIdeal.under R)) (Localization.AtPrime q.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver _ _
    refine Algebra.IsSeparable.of_equiv_equiv (RingEquiv.ofBijective e₁ hb₁)
      (RingEquiv.ofBijective e₂ hb₂) ?_
    apply Ideal.ResidueField.ringHom_ext
    ext r
    simp only [RingHom.comp_apply, RingHom.coe_coe, RingEquiv.ofBijective_apply]
    have hA : ∀ x, algebraMap (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField x =
        Ideal.ResidueField.map (q.asIdeal.under R) q.asIdeal (algebraMap R S) rfl x :=
      fun _ ↦ rfl
    have hB : ∀ x, algebraMap (m.under Rₚ).ResidueField m.ResidueField x =
        Ideal.ResidueField.map (m.under Rₚ) m (algebraMap Rₚ Sₚ) rfl x :=
      fun _ ↦ rfl
    rw [hA, hB]
    simp only [e₁, e₂, Ideal.ResidueField.map_algebraMap]
    rw [← IsScalarTower.algebraMap_apply R Rₚ Sₚ,
      ← IsScalarTower.algebraMap_apply R Sₚ m.ResidueField]
    rw [← IsScalarTower.algebraMap_apply R S Sₚ,
      ← IsScalarTower.algebraMap_apply R Sₚ m.ResidueField]

end TameLocalization

end Pcf.Stacks.SchemeLevel.AffineTame
