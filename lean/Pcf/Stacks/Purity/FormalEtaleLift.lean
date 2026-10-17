/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Pcf.Stacks.Purity.FiniteModuleHartogs

/-!
# Formally étale lifting of algebra maps glued along a regular pair

This file contains the commutative algebra behind the complete-regular-local case of the
hypersurface lifting step in Zariski–Nagata purity (Stacks Tags `0BLM`/`0BM6`), formulated
without local cohomology.

Let `A` be a commutative ring, `B` and `C` two `A`-algebras and `f, x, y ∈ A`.  Write
`Mₙ = C / f^(n+1) C` and `N = C / f C`.  Suppose that

* `B` becomes formally étale over `A` after inverting `x`, after inverting `y`, and formally
  unramified after inverting `x * y` (this is what "`Spec B` is étale over the open
  `D(x) ∪ D(y)`" gives);
* `x, y` is a regular pair on every `Mₙ` and `x` is regular on `N`
  (this is what "`f^(n+1), x, y` is a regular sequence on `C`" gives).

Then every `A`-algebra map `φ₀ : B → N` lifts uniquely to `Mₙ` for each `n`:

1. on `D(x)` the lift exists by formal smoothness of `B_x` along the nilpotent kernel of
   `(Mₙ)_x → N_x`, and is unique by formal unramifiedness;
2. the lifts on `D(x)` and `D(y)` agree on `D(xy)` by uniqueness there;
3. the regular pair `x, y` on `Mₙ` makes `Mₙ → (Mₙ)_x × (Mₙ)_y → (Mₙ)_{xy}` exact
   (`exists_common_value_of_module_regular_pair`), so the two local lifts glue to a map
   `B → Mₙ`; uniqueness follows from uniqueness on `D(x)` and injectivity of `Mₙ → (Mₙ)_x`.

If moreover `C` is `(f)`-adically complete, the unique lifts are compatible and converge to an
`A`-algebra map `B → C` lifting `φ₀` (`exists_algHom_lift_of_isAdicComplete`).

Nothing here uses normality, Noetherianity or dimension; those enter only when the hypotheses
are verified for a finite normal algebra over a complete regular local ring, in
`Pcf.Stacks.Purity.HypersurfaceLiftingComplete`.
-/

@[expose] public section

noncomputable section

set_option linter.style.haveILetI false

open scoped Pointwise

universe u v w x

namespace Pcf.Stacks

/-! ### Regularity on quotient rings, via ideal membership -/

section QuotientRegular

variable {A : Type u} [CommRing A] {C : Type v} [CommRing C] [Algebra A C]

/-- The quotient map of an `A`-algebra by an ideal is `A`-linear. -/
theorem Ideal.Quotient.mk_smul_base (J : Ideal C) (a : A) (c : C) :
    Ideal.Quotient.mk J (a • c) = a • Ideal.Quotient.mk J c := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, Ideal.Quotient.mk_algebraMap]

/-- Membership in a pointwise scalar multiple of the full submodule. -/
theorem mem_smul_top_iff_exists {M : Type w} [AddCommGroup M] [Module A M] (a : A) (m : M) :
    m ∈ a • (⊤ : Submodule A M) ↔ ∃ m' : M, a • m' = m := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  simp

/-- A base element acts regularly on a quotient ring as soon as multiplication by it reflects
membership in the ideal. -/
theorem isSMulRegular_quotient_of_forall (J : Ideal C) (a : A)
    (h : ∀ c : C, a • c ∈ J → c ∈ J) : IsSMulRegular (C ⧸ J) a := by
  intro u v huv
  change a • u = a • v at huv
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective v
  rw [← Ideal.Quotient.mk_smul_base, ← Ideal.Quotient.mk_smul_base, Ideal.Quotient.eq] at huv
  rw [Ideal.Quotient.eq]
  apply h
  rwa [smul_sub]

/-- Conversely, regularity on a quotient ring gives the membership reflection. -/
theorem forall_of_isSMulRegular_quotient (J : Ideal C) (a : A)
    (h : IsSMulRegular (C ⧸ J) a) : ∀ c : C, a • c ∈ J → c ∈ J := by
  intro c hc
  have h0 : a • (Ideal.Quotient.mk J c) = a • (0 : C ⧸ J) := by
    rw [smul_zero, ← Ideal.Quotient.mk_smul_base]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hc
  exact Ideal.Quotient.eq_zero_iff_mem.mp (h h0)

/-- A base element `y` acts regularly on `(C / J) / x (C / J)` as soon as multiplication by `y`
reflects membership in `J + x C`. -/
theorem isSMulRegular_quotSMulTop_quotient_of_forall (J : Ideal C) (x y : A)
    (h : ∀ c : C, y • c ∈ J ⊔ Ideal.span {algebraMap A C x} →
      c ∈ J ⊔ Ideal.span {algebraMap A C x}) :
    IsSMulRegular (QuotSMulTop x (C ⧸ J)) y := by
  intro u v huv
  change y • u = y • v at huv
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective v
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
    ← smul_sub, mem_smul_top_iff_exists] at huv
  obtain ⟨w, hw⟩ := huv
  obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective w
  rw [Submodule.Quotient.eq, mem_smul_top_iff_exists]
  rw [← Ideal.Quotient.mk_smul_base, ← map_sub, ← Ideal.Quotient.mk_smul_base,
    Ideal.Quotient.eq] at hw
  have hmem : y • (c - d) ∈ J ⊔ Ideal.span {algebraMap A C x} := by
    have h1 : y • (c - d) = (x • e - y • (c - d)) * (-1) + x • e := by ring
    rw [h1]
    refine Submodule.add_mem _ (Ideal.mem_sup_left (J.mul_mem_right _ hw)) ?_
    apply Ideal.mem_sup_right
    rw [Ideal.mem_span_singleton']
    exact ⟨e, by rw [Algebra.smul_def, mul_comm]⟩
  obtain ⟨j, hj, z, hz, hjz⟩ := Submodule.mem_sup.mp (h _ hmem)
  obtain ⟨e', he'⟩ := Ideal.mem_span_singleton'.mp hz
  refine ⟨Ideal.Quotient.mk J e', ?_⟩
  rw [← Ideal.Quotient.mk_smul_base, ← map_sub, Ideal.Quotient.eq]
  have : x • e' - (c - d) = -j := by
    rw [← hjz, ← he', Algebra.smul_def, mul_comm]
    ring
  rw [this]
  exact J.neg_mem hj

end QuotientRegular

/-! ### Gluing algebra maps along a regular pair -/

section Glue

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
variable {M : Type w} [CommRing M] [Algebra A M]

/-- The image of a base element acting regularly is a nonzerodivisor of the algebra. -/
theorem algebraMap_mem_nonZeroDivisors_of_isSMulRegular {a : A} (ha : IsSMulRegular M a) :
    algebraMap A M a ∈ nonZeroDivisors M := by
  rw [mem_nonZeroDivisors_iff]
  refine ⟨fun m hm ↦ ?_, fun m hm ↦ ?_⟩
  · apply ha
    change a • m = a • (0 : M)
    rw [smul_zero, Algebra.smul_def]
    exact hm
  · apply ha
    change a • m = a • (0 : M)
    rw [smul_zero, Algebra.smul_def, mul_comm]
    exact hm

/-- Localizing away from the image of a regular base element is injective. -/
theorem algebraMap_localization_away_injective {a : A} (ha : IsSMulRegular M a) :
    Function.Injective (algebraMap M (Localization.Away (algebraMap A M a))) := by
  apply IsLocalization.injective (M := Submonoid.powers (algebraMap A M a))
  rintro _ ⟨n, rfl⟩
  exact pow_mem (algebraMap_mem_nonZeroDivisors_of_isSMulRegular ha) n

/-- Two `A`-algebra maps into `M_x` and `M_y` that agree in `M_{xy}` come from a single map into
`M`, provided `x, y` is a regular pair on `M`.  This is the ring-level form of the depth-two
Hartogs intersection used to glue local lifts. -/
theorem exists_algHom_of_regular_pair_of_agree
    {x y : A} (hx : IsSMulRegular M x) (hy : IsSMulRegular M y)
    (hxy : IsSMulRegular (QuotSMulTop x M) y)
    (ψx : B →ₐ[A] Localization.Away (algebraMap A M x))
    (ψy : B →ₐ[A] Localization.Away (algebraMap A M y))
    (hagree : ∀ b : B,
      IsLocalization.Away.awayToAwayRight
          (P := Localization.Away (algebraMap A M x * algebraMap A M y))
          (algebraMap A M x) (algebraMap A M y) (ψx b) =
        IsLocalization.Away.awayToAwayLeft
          (P := Localization.Away (algebraMap A M x * algebraMap A M y))
          (algebraMap A M y) (algebraMap A M x) (ψy b)) :
    ∃ φ : B →ₐ[A] M, ∀ b : B,
      algebraMap M (Localization.Away (algebraMap A M x)) (φ b) = ψx b ∧
        algebraMap M (Localization.Away (algebraMap A M y)) (φ b) = ψy b := by
  let Mx := Localization.Away (algebraMap A M x)
  let My := Localization.Away (algebraMap A M y)
  let Mxy := Localization.Away (algebraMap A M x * algebraMap A M y)
  have hinjx : Function.Injective (algebraMap M Mx) := algebraMap_localization_away_injective hx
  have hxyreg : IsSMulRegular M (x * y) := by
    intro m m' h
    apply hy
    apply hx
    simpa only [smul_smul] using h
  have hinjxy : Function.Injective (algebraMap M Mxy) := by
    have := algebraMap_localization_away_injective (M := M) hxyreg
    rwa [map_mul] at this
  -- the key pointwise statement
  have key : ∀ b : B, ∃ c : M, algebraMap M Mx c = ψx b ∧ algebraMap M My c = ψy b := by
    intro b
    obtain ⟨u, n, hu⟩ : ∃ (u : M) (n : ℕ),
        ψx b * algebraMap M Mx (algebraMap A M x ^ n) = algebraMap M Mx u :=
      ⟨_, _, IsLocalization.Away.sec_spec (algebraMap A M x) (ψx b)⟩
    obtain ⟨v, m, hv⟩ : ∃ (v : M) (m : ℕ),
        ψy b * algebraMap M My (algebraMap A M y ^ m) = algebraMap M My v :=
      ⟨_, _, IsLocalization.Away.sec_spec (algebraMap A M y) (ψy b)⟩
    have hcross : y ^ m • u = x ^ n • v := by
      apply hinjxy
      have hu' := congrArg
        (IsLocalization.Away.awayToAwayRight (P := Mxy) (algebraMap A M x) (algebraMap A M y)) hu
      have hv' := congrArg
        (IsLocalization.Away.awayToAwayLeft (P := Mxy) (algebraMap A M y) (algebraMap A M x)) hv
      rw [map_mul, IsLocalization.Away.awayToAwayRight_eq, IsLocalization.Away.awayToAwayRight_eq,
        hagree b] at hu'
      rw [map_mul, IsLocalization.Away.awayToAwayLeft_eq, IsLocalization.Away.awayToAwayLeft_eq]
        at hv'
      rw [map_pow] at hu' hv'
      simp only [Algebra.smul_def, map_mul, map_pow]
      rw [← hu', ← hv']
      ring
    obtain ⟨c, hcu, hcv⟩ := exists_common_value_of_module_regular_pair hx hxy m n hcross
    refine ⟨c, ?_, ?_⟩
    · have hunit : IsUnit (algebraMap M Mx (algebraMap A M x ^ n)) :=
        IsLocalization.map_units Mx
          ⟨algebraMap A M x ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers _) n⟩
      apply hunit.mul_right_cancel
      rw [hu, hcu, Algebra.smul_def]
      simp only [map_mul, map_pow]
      ring
    · have hunit : IsUnit (algebraMap M My (algebraMap A M y ^ m)) :=
        IsLocalization.map_units My
          ⟨algebraMap A M y ^ m, Submonoid.pow_mem _ (Submonoid.mem_powers _) m⟩
      apply hunit.mul_right_cancel
      rw [hv, hcv, Algebra.smul_def]
      simp only [map_mul, map_pow]
      ring
  choose φ hφ using key
  have hφx : ∀ b, algebraMap M Mx (φ b) = ψx b := fun b ↦ (hφ b).1
  let φ' : B →ₐ[A] M :=
    { toFun := φ
      map_one' := by
        apply hinjx
        rw [hφx, map_one, map_one]
      map_mul' := fun b₁ b₂ ↦ by
        apply hinjx
        rw [hφx, map_mul, map_mul, hφx, hφx]
      map_zero' := by
        apply hinjx
        rw [hφx, map_zero, map_zero]
      map_add' := fun b₁ b₂ ↦ by
        apply hinjx
        rw [hφx, map_add, map_add, hφx, hφx]
      commutes' := fun a ↦ by
        apply hinjx
        rw [hφx, AlgHom.commutes, ← IsScalarTower.algebraMap_apply] }
  exact ⟨φ', hφ⟩

end Glue

/-! ### Localizing a surjection with nilpotent kernel -/

section LocalizedKernel

variable {A : Type u} [CommRing A]
variable {M : Type w} [CommRing M] [Algebra A M] {N : Type x} [CommRing N] [Algebra A N]
variable (π : M →ₐ[A] N) (r : M)
variable (Mr : Type*) [CommRing Mr] [Algebra M Mr] [Algebra A Mr] [IsScalarTower A M Mr]
  [IsLocalization.Away r Mr]
variable (Nr : Type*) [CommRing Nr] [Algebra N Nr] [Algebra A Nr] [IsScalarTower A N Nr]
  [IsLocalization.Away (π r) Nr]

/-- The kernel of the localization of an algebra map is contained in the localization of the
kernel. -/
theorem ker_away_mapₐ_le :
    RingHom.ker (IsLocalization.Away.mapₐ Mr Nr π r) ≤
      (RingHom.ker π).map (algebraMap M Mr) := by
  intro z hz
  obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers r) z
  change IsLocalization.mk' Mr m s ∈ _
  rw [RingHom.mem_ker, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map,
    IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff] at hz
  obtain ⟨⟨t, j, rfl⟩, ht⟩ := hz
  have hmem : r ^ j * m ∈ RingHom.ker π := by
    rw [RingHom.mem_ker, map_mul, map_pow]
    exact ht
  have hz' : IsLocalization.mk' Mr m s =
      algebraMap M Mr (r ^ j * m) * IsLocalization.mk' Mr 1 (⟨r ^ j, j, rfl⟩ * s) := by
    rw [← IsLocalization.mk'_eq_mul_mk'_one, mul_comm (r ^ j) m, ← IsLocalization.mk'_cancel m s
      ⟨r ^ j, j, rfl⟩]
    congr 1
    exact mul_comm _ _
  rw [hz']
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hmem)

/-- Localizing a surjection with nilpotent kernel keeps the kernel nilpotent. -/
theorem isNilpotent_ker_away_mapₐ (hker : IsNilpotent (RingHom.ker π)) :
    IsNilpotent (RingHom.ker (IsLocalization.Away.mapₐ Mr Nr π r)) := by
  obtain ⟨k, hk⟩ := hker
  refine ⟨k, le_bot_iff.mp ?_⟩
  calc RingHom.ker (IsLocalization.Away.mapₐ Mr Nr π r) ^ k
      ≤ ((RingHom.ker π).map (algebraMap M Mr)) ^ k :=
        Ideal.pow_right_mono (ker_away_mapₐ_le π r Mr Nr) k
    _ = ((RingHom.ker π) ^ k).map (algebraMap M Mr) := (Ideal.map_pow _ _ _).symm
    _ = ⊥ := by rw [hk, Ideal.zero_eq_bot, Ideal.map_bot]

/-- The localization of an algebra map, evaluated on the image of the source ring. -/
theorem away_mapₐ_algebraMap (m : M) :
    IsLocalization.Away.mapₐ Mr Nr π r (algebraMap M Mr m) = algebraMap N Nr (π m) := by
  rw [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map, IsLocalization.map_eq]
  rfl

variable {r}

/-- `A`-algebra form of `IsLocalization.Away.awayToAwayRight`. -/
def awayToAwayRightₐ (r s : M) : Localization.Away r →ₐ[A] Localization.Away (r * s) :=
  { IsLocalization.Away.awayToAwayRight (P := Localization.Away (r * s)) r s with
    commutes' := fun a ↦ by
      change IsLocalization.Away.awayToAwayRight (P := Localization.Away (r * s)) r s
        (algebraMap A (Localization.Away r) a) = _
      rw [IsScalarTower.algebraMap_apply A M (Localization.Away r),
        IsLocalization.Away.awayToAwayRight_eq, ← IsScalarTower.algebraMap_apply] }

/-- `A`-algebra form of `IsLocalization.Away.awayToAwayLeft`. -/
def awayToAwayLeftₐ (r s : M) : Localization.Away s →ₐ[A] Localization.Away (r * s) :=
  { IsLocalization.Away.awayToAwayLeft (P := Localization.Away (r * s)) s r with
    commutes' := fun a ↦ by
      change IsLocalization.Away.awayToAwayLeft (P := Localization.Away (r * s)) s r
        (algebraMap A (Localization.Away s) a) = _
      rw [IsScalarTower.algebraMap_apply A M (Localization.Away s),
        IsLocalization.Away.awayToAwayLeft_eq, ← IsScalarTower.algebraMap_apply] }

theorem awayToAwayRightₐ_algebraMap (r s : M) (m : M) :
    awayToAwayRightₐ (A := A) r s (algebraMap M (Localization.Away r) m) =
      algebraMap M (Localization.Away (r * s)) m :=
  IsLocalization.Away.awayToAwayRight_eq r s m

theorem awayToAwayLeftₐ_algebraMap (r s : M) (m : M) :
    awayToAwayLeftₐ (A := A) r s (algebraMap M (Localization.Away s) m) =
      algebraMap M (Localization.Away (r * s)) m :=
  IsLocalization.Away.awayToAwayLeft_eq s r m

/-- Two algebra maps out of a localization away from an element agree once they agree on the
image of the ring. -/
theorem away_algHom_ext {P : Type*} [CommRing P] [Algebra A P] (r : M)
    {j k : Localization.Away r →ₐ[A] P}
    (h : ∀ m, j (algebraMap M (Localization.Away r) m) = k (algebraMap M (Localization.Away r) m)) :
    j = k :=
  AlgHom.toRingHom_injective
    (IsLocalization.ringHom_ext (Submonoid.powers r) (RingHom.ext h))

end LocalizedKernel

/-! ### The formally étale lift along a regular pair -/

section Lift

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
variable {M : Type w} [CommRing M] [Algebra A M] {N : Type x} [CommRing N] [Algebra A N]

/-- Uniqueness of lifts: two `A`-algebra maps `B → M` that agree after composing with a map
`π : M → N` with nilpotent kernel are equal, provided `B_x` is formally unramified over `A` and
`x` is regular on `M`. -/
theorem algHom_lift_unique_of_formallyUnramified
    (π : M →ₐ[A] N) (hker : IsNilpotent (RingHom.ker π)) {x : A}
    [Algebra.FormallyUnramified A (Localization.Away (algebraMap A B x))]
    (hx : IsSMulRegular M x) {φ φ' : B →ₐ[A] M} (h : π.comp φ = π.comp φ') : φ = φ' := by
  let Bx := Localization.Away (algebraMap A B x)
  let Mx := Localization.Away (algebraMap A M x)
  let Nx := Localization.Away (algebraMap A N x)
  haveI : IsLocalization.Away (π (algebraMap A M x)) Nx := by
    rw [AlgHom.commutes]
    infer_instance
  let πx : Mx →ₐ[A] Nx := IsLocalization.Away.mapₐ Mx Nx π (algebraMap A M x)
  have hπx : ∀ m, πx (algebraMap M Mx m) = algebraMap N Nx (π m) := fun m ↦
    away_mapₐ_algebraMap π _ Mx Nx m
  have hnil : IsNilpotent (RingHom.ker πx) := isNilpotent_ker_away_mapₐ π _ Mx Nx hker
  have hinj : Function.Injective (algebraMap M Mx) := algebraMap_localization_away_injective hx
  have hunit : ∀ φ'' : B →ₐ[A] M,
      IsUnit (((IsScalarTower.toAlgHom A M Mx).comp φ'') (algebraMap A B x)) := by
    intro φ''
    change IsUnit (algebraMap M Mx (φ'' (algebraMap A B x)))
    rw [AlgHom.commutes φ'' x]
    exact IsLocalization.Away.algebraMap_isUnit _
  let ψ : Bx →ₐ[A] Mx := IsLocalization.Away.liftAlgHom (algebraMap A B x) (hunit φ)
  let ψ' : Bx →ₐ[A] Mx := IsLocalization.Away.liftAlgHom (algebraMap A B x) (hunit φ')
  have hψ : ∀ b, ψ (algebraMap B Bx b) = algebraMap M Mx (φ b) := fun b ↦
    IsLocalization.Away.lift_eq (algebraMap A B x) (hunit φ) b
  have hψ' : ∀ b, ψ' (algebraMap B Bx b) = algebraMap M Mx (φ' b) := fun b ↦
    IsLocalization.Away.lift_eq (algebraMap A B x) (hunit φ') b
  have hcomp : πx.comp ψ = πx.comp ψ' := by
    apply away_algHom_ext
    intro b
    change πx (ψ (algebraMap B Bx b)) = πx (ψ' (algebraMap B Bx b))
    rw [hψ, hψ', hπx, hπx]
    congr 1
    exact AlgHom.congr_fun h b
  have hψψ' : ψ = ψ' := Algebra.FormallyUnramified.lift_unique' πx hnil ψ ψ' hcomp
  ext b
  apply hinj
  rw [← hψ, ← hψ', hψψ']

/-- Existence of lifts along a surjection with nilpotent kernel, glued from the two formally
étale localizations `B_x`, `B_y` using the regular pair `x, y` on `M`. -/
theorem exists_algHom_lift_of_regular_pair
    (π : M →ₐ[A] N) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    {x y : A}
    [Algebra.FormallyEtale A (Localization.Away (algebraMap A B x))]
    [Algebra.FormallyEtale A (Localization.Away (algebraMap A B y))]
    [Algebra.FormallyUnramified A (Localization.Away (algebraMap A B (x * y)))]
    (hx : IsSMulRegular M x) (hy : IsSMulRegular M y)
    (hxy : IsSMulRegular (QuotSMulTop x M) y)
    (hxN : IsSMulRegular N x)
    (φ₀ : B →ₐ[A] N) :
    ∃ φ : B →ₐ[A] M, π.comp φ = φ₀ := by
  -- the localized rings
  let Bx := Localization.Away (algebraMap A B x)
  let By := Localization.Away (algebraMap A B y)
  let Bxy := Localization.Away (algebraMap A B (x * y))
  let Mx := Localization.Away (algebraMap A M x)
  let My := Localization.Away (algebraMap A M y)
  let Mxy := Localization.Away (algebraMap A M x * algebraMap A M y)
  let Nx := Localization.Away (algebraMap A N x)
  let Ny := Localization.Away (algebraMap A N y)
  let Nxy := Localization.Away (algebraMap A N x * algebraMap A N y)
  haveI : IsLocalization.Away (π (algebraMap A M x)) Nx := by
    rw [AlgHom.commutes]
    infer_instance
  haveI : IsLocalization.Away (π (algebraMap A M y)) Ny := by
    rw [AlgHom.commutes]
    infer_instance
  haveI : IsLocalization.Away (π (algebraMap A M x * algebraMap A M y)) Nxy := by
    rw [map_mul, AlgHom.commutes, AlgHom.commutes]
    infer_instance
  haveI : IsLocalization.Away (π (algebraMap A M x) * π (algebraMap A M y)) Nxy := by
    rw [AlgHom.commutes, AlgHom.commutes]
    infer_instance
  -- the localized surjections
  let πx : Mx →ₐ[A] Nx := IsLocalization.Away.mapₐ Mx Nx π (algebraMap A M x)
  let πy : My →ₐ[A] Ny := IsLocalization.Away.mapₐ My Ny π (algebraMap A M y)
  let πxy : Mxy →ₐ[A] Nxy :=
    IsLocalization.Away.mapₐ Mxy Nxy π (algebraMap A M x * algebraMap A M y)
  have hπx : ∀ m, πx (algebraMap M Mx m) = algebraMap N Nx (π m) := fun m ↦
    away_mapₐ_algebraMap π _ Mx Nx m
  have hπy : ∀ m, πy (algebraMap M My m) = algebraMap N Ny (π m) := fun m ↦
    away_mapₐ_algebraMap π _ My Ny m
  have hπxy : ∀ m, πxy (algebraMap M Mxy m) = algebraMap N Nxy (π m) := fun m ↦
    away_mapₐ_algebraMap π _ Mxy Nxy m
  have hnilx : IsNilpotent (RingHom.ker πx) := isNilpotent_ker_away_mapₐ π _ Mx Nx hker
  have hnily : IsNilpotent (RingHom.ker πy) := isNilpotent_ker_away_mapₐ π _ My Ny hker
  have hnilxy : IsNilpotent (RingHom.ker πxy) := isNilpotent_ker_away_mapₐ π _ Mxy Nxy hker
  have hsurjx : Function.Surjective πx :=
    IsLocalization.Away.mapₐ_surjective_of_surjective _ hπ
  have hsurjy : Function.Surjective πy :=
    IsLocalization.Away.mapₐ_surjective_of_surjective _ hπ
  -- the given map, localized
  have hunitx : IsUnit (((IsScalarTower.toAlgHom A N Nx).comp φ₀) (algebraMap A B x)) := by
    change IsUnit (algebraMap N Nx (φ₀ (algebraMap A B x)))
    rw [AlgHom.commutes φ₀ x]
    exact IsLocalization.Away.algebraMap_isUnit _
  have hunity : IsUnit (((IsScalarTower.toAlgHom A N Ny).comp φ₀) (algebraMap A B y)) := by
    change IsUnit (algebraMap N Ny (φ₀ (algebraMap A B y)))
    rw [AlgHom.commutes φ₀ y]
    exact IsLocalization.Away.algebraMap_isUnit _
  let gx : Bx →ₐ[A] Nx := IsLocalization.Away.liftAlgHom (algebraMap A B x) hunitx
  let gy : By →ₐ[A] Ny := IsLocalization.Away.liftAlgHom (algebraMap A B y) hunity
  have hgx : ∀ b, gx (algebraMap B Bx b) = algebraMap N Nx (φ₀ b) := fun b ↦
    IsLocalization.Away.lift_eq (algebraMap A B x) hunitx b
  have hgy : ∀ b, gy (algebraMap B By b) = algebraMap N Ny (φ₀ b) := fun b ↦
    IsLocalization.Away.lift_eq (algebraMap A B y) hunity b
  -- the local lifts
  let ψx : Bx →ₐ[A] Mx := Algebra.FormallySmooth.liftOfSurjective gx πx hsurjx hnilx
  let ψy : By →ₐ[A] My := Algebra.FormallySmooth.liftOfSurjective gy πy hsurjy hnily
  have hψx : ∀ z, πx (ψx z) = gx z := fun z ↦
    Algebra.FormallySmooth.liftOfSurjective_apply gx πx hsurjx hnilx z
  have hψy : ∀ z, πy (ψy z) = gy z := fun z ↦
    Algebra.FormallySmooth.liftOfSurjective_apply gy πy hsurjy hnily z
  let ψx' : B →ₐ[A] Mx := ψx.comp (IsScalarTower.toAlgHom A B Bx)
  let ψy' : B →ₐ[A] My := ψy.comp (IsScalarTower.toAlgHom A B By)
  -- the comparison maps into the common localization
  let ρx : Mx →ₐ[A] Mxy := awayToAwayRightₐ (algebraMap A M x) (algebraMap A M y)
  let ρy : My →ₐ[A] Mxy := awayToAwayLeftₐ (algebraMap A M x) (algebraMap A M y)
  have hρx : ∀ m, ρx (algebraMap M Mx m) = algebraMap M Mxy m := fun m ↦
    awayToAwayRightₐ_algebraMap _ _ m
  have hρy : ∀ m, ρy (algebraMap M My m) = algebraMap M Mxy m := fun m ↦
    awayToAwayLeftₐ_algebraMap _ _ m
  let σx : Nx →+* Nxy :=
    IsLocalization.Away.awayToAwayRight (P := Nxy) (π (algebraMap A M x)) (π (algebraMap A M y))
  let σy : Ny →+* Nxy :=
    IsLocalization.Away.awayToAwayLeft (P := Nxy) (π (algebraMap A M y)) (π (algebraMap A M x))
  have hσx : ∀ n, σx (algebraMap N Nx n) = algebraMap N Nxy n := fun n ↦
    IsLocalization.Away.awayToAwayRight_eq _ _ n
  have hσy : ∀ n, σy (algebraMap N Ny n) = algebraMap N Nxy n := fun n ↦
    IsLocalization.Away.awayToAwayLeft_eq _ _ n
  have hux : IsUnit (algebraMap N Nxy (π (algebraMap A M x))) := by
    have hunit : IsUnit (algebraMap N Nxy (π (algebraMap A M x) * π (algebraMap A M y))) :=
      IsLocalization.Away.algebraMap_isUnit _
    rw [map_mul] at hunit
    exact isUnit_of_mul_isUnit_left hunit
  have huy : IsUnit (algebraMap N Nxy (π (algebraMap A M y))) := by
    have hunit : IsUnit (algebraMap N Nxy (π (algebraMap A M x) * π (algebraMap A M y))) :=
      IsLocalization.Away.algebraMap_isUnit _
    rw [map_mul] at hunit
    exact isUnit_of_mul_isUnit_right hunit
  have hsquarex : ∀ z : Mx, πxy (ρx z) = σx (πx z) := by
    intro z
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (algebraMap A M x)) z
    have h1 : IsLocalization.mk' Mx m s * algebraMap M Mx (s : M) = algebraMap M Mx m :=
      IsLocalization.mk'_spec Mx m s
    have h2 := congrArg (fun z : Mx ↦ πxy (ρx z)) h1
    have h3 := congrArg (fun z : Mx ↦ σx (πx z)) h1
    simp only [map_mul] at h2 h3
    rw [hρx, hρx, hπxy, hπxy] at h2
    rw [hπx, hπx, hσx, hσx] at h3
    have hu : IsUnit (algebraMap N Nxy (π (s : M))) := by
      obtain ⟨n, hn⟩ := s.2
      rw [← hn, map_pow, map_pow]
      exact hux.pow n
    exact hu.mul_right_cancel (h2.trans h3.symm)
  have hsquarey : ∀ z : My, πxy (ρy z) = σy (πy z) := by
    intro z
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (algebraMap A M y)) z
    have h1 : IsLocalization.mk' My m s * algebraMap M My (s : M) = algebraMap M My m :=
      IsLocalization.mk'_spec My m s
    have h2 := congrArg (fun z : My ↦ πxy (ρy z)) h1
    have h3 := congrArg (fun z : My ↦ σy (πy z)) h1
    simp only [map_mul] at h2 h3
    rw [hρy, hρy, hπxy, hπxy] at h2
    rw [hπy, hπy, hσy, hσy] at h3
    have hu : IsUnit (algebraMap N Nxy (π (s : M))) := by
      obtain ⟨n, hn⟩ := s.2
      rw [← hn, map_pow, map_pow]
      exact huy.pow n
    exact hu.mul_right_cancel (h2.trans h3.symm)
  -- the two local lifts agree on `D(xy)`, by uniqueness there
  have hunitΘ : ∀ ψ'' : B →ₐ[A] Mxy, IsUnit (ψ'' (algebraMap A B (x * y))) := by
    intro ψ''
    rw [AlgHom.commutes ψ'' (x * y), IsScalarTower.algebraMap_apply A M Mxy, map_mul]
    exact IsLocalization.Away.algebraMap_isUnit _
  let Θx : Bxy →ₐ[A] Mxy :=
    IsLocalization.Away.liftAlgHom (algebraMap A B (x * y)) (hunitΘ (ρx.comp ψx'))
  let Θy : Bxy →ₐ[A] Mxy :=
    IsLocalization.Away.liftAlgHom (algebraMap A B (x * y)) (hunitΘ (ρy.comp ψy'))
  have hΘx : ∀ b, Θx (algebraMap B Bxy b) = ρx (ψx' b) := fun b ↦
    IsLocalization.Away.lift_eq (algebraMap A B (x * y)) (hunitΘ (ρx.comp ψx')) b
  have hΘy : ∀ b, Θy (algebraMap B Bxy b) = ρy (ψy' b) := fun b ↦
    IsLocalization.Away.lift_eq (algebraMap A B (x * y)) (hunitΘ (ρy.comp ψy')) b
  have hΘ : Θx = Θy := by
    apply Algebra.FormallyUnramified.lift_unique' πxy hnilxy
    apply away_algHom_ext
    intro b
    change πxy (Θx (algebraMap B Bxy b)) = πxy (Θy (algebraMap B Bxy b))
    rw [hΘx, hΘy, hsquarex, hsquarey]
    change σx (πx (ψx (algebraMap B Bx b))) = σy (πy (ψy (algebraMap B By b)))
    rw [hψx, hψy, hgx, hgy, hσx, hσy]
  have hagree : ∀ b : B,
      IsLocalization.Away.awayToAwayRight (P := Mxy) (algebraMap A M x) (algebraMap A M y)
          (ψx' b) =
        IsLocalization.Away.awayToAwayLeft (P := Mxy) (algebraMap A M y) (algebraMap A M x)
          (ψy' b) := by
    intro b
    have := congrArg (fun Θ : Bxy →ₐ[A] Mxy ↦ Θ (algebraMap B Bxy b)) hΘ
    simp only [hΘx, hΘy] at this
    exact this
  -- glue
  obtain ⟨φ, hφ⟩ := exists_algHom_of_regular_pair_of_agree hx hy hxy ψx' ψy' hagree
  refine ⟨φ, ?_⟩
  ext b
  have hinjN : Function.Injective (algebraMap N Nx) := algebraMap_localization_away_injective hxN
  apply hinjN
  rw [AlgHom.comp_apply, ← hπx, (hφ b).1]
  change πx (ψx (algebraMap B Bx b)) = _
  rw [hψx, hgx]

end Lift

/-! ### The tower of thickenings and the limit -/

section Tower

variable {A : Type u} [CommRing A] {C : Type w} [CommRing C] [Algebra A C]

/-- The `A`-algebra map between quotients of `C` by nested ideals. -/
def quotFactorₐ {I J : Ideal C} (h : I ≤ J) : (C ⧸ I) →ₐ[A] C ⧸ J :=
  Ideal.Quotient.liftₐ I (Ideal.Quotient.mkₐ A J)
    (fun _ ha ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (h ha))

@[simp]
theorem quotFactorₐ_mk {I J : Ideal C} (h : I ≤ J) (c : C) :
    quotFactorₐ (A := A) h (Ideal.Quotient.mk I c) = Ideal.Quotient.mk J c :=
  rfl

theorem quotFactorₐ_surjective {I J : Ideal C} (h : I ≤ J) :
    Function.Surjective (quotFactorₐ (A := A) h) := by
  intro z
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨Ideal.Quotient.mk I c, quotFactorₐ_mk h c⟩

theorem quotFactorₐ_comp_quotFactorₐ {I J K : Ideal C} (hIJ : I ≤ J) (hJK : J ≤ K) :
    (quotFactorₐ (A := A) hJK).comp (quotFactorₐ hIJ) = quotFactorₐ (hIJ.trans hJK) := by
  apply AlgHom.ext
  intro c
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  rfl

theorem quotFactorₐ_self {I : Ideal C} (c : C ⧸ I) :
    quotFactorₐ (A := A) (le_refl I) c = c := by
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  rfl

variable (f : A)

/-- `C / f^(n+1) C` maps onto `C / f C`. -/
theorem span_pow_succ_le {n : ℕ} :
    Ideal.span {algebraMap A C f ^ (n + 1)} ≤ Ideal.span {algebraMap A C f} :=
  Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self _ (Nat.succ_ne_zero n))

/-- `C / f^(n+2) C` maps onto `C / f^(n+1) C`. -/
theorem span_pow_succ_succ_le (n : ℕ) :
    Ideal.span {algebraMap A C f ^ (n + 2)} ≤ Ideal.span {algebraMap A C f ^ (n + 1)} :=
  Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (by omega))

/-- Nested thickenings. -/
theorem span_pow_succ_le_of_le {m n : ℕ} (h : m ≤ n) :
    Ideal.span {algebraMap A C f ^ (n + 1)} ≤ Ideal.span {algebraMap A C f ^ (m + 1)} :=
  Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (by omega))

/-- The kernel of `C / f^(n+1) C → C / f C` is nilpotent. -/
theorem isNilpotent_ker_quotFactorₐ_span_pow (n : ℕ) :
    IsNilpotent (RingHom.ker (quotFactorₐ (A := A) (span_pow_succ_le (C := C) f (n := n)))) := by
  set I := Ideal.span {algebraMap A C f ^ (n + 1)}
  have hle : RingHom.ker (quotFactorₐ (A := A) (span_pow_succ_le (C := C) f (n := n))) ≤
      Ideal.span {Ideal.Quotient.mk I (algebraMap A C f)} := by
    intro z hz
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [RingHom.mem_ker, quotFactorₐ_mk, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton'] at hz
    obtain ⟨a, rfl⟩ := hz
    rw [map_mul, Ideal.mem_span_singleton']
    exact ⟨_, rfl⟩
  refine ⟨n + 1, le_bot_iff.mp (le_trans (Ideal.pow_right_mono hle (n + 1)) ?_)⟩
  rw [Ideal.span_singleton_pow, ← map_pow (Ideal.Quotient.mk I) (algebraMap A C f) (n + 1)]
  exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_bot.mpr
    (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _))))

/-- Membership in the `(f)`-adic filtration of `C`, in ideal terms. -/
theorem mem_span_pow_smul_top_iff (n : ℕ) (c : C) :
    c ∈ (Ideal.span {f} ^ n • ⊤ : Submodule A C) ↔ c ∈ Ideal.span {algebraMap A C f ^ n} := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, mem_smul_top_iff_exists,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c', rfl⟩
    exact ⟨c', by rw [Algebra.smul_def, map_pow, mul_comm]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, by rw [Algebra.smul_def, map_pow, mul_comm]⟩

variable {B : Type v} [CommRing B] [Algebra A B]

/-- A compatible family of `A`-algebra maps `B → C / f^(n+1) C` converges to an `A`-algebra map
`B → C` when `C` is `(f)`-adically complete. -/
theorem exists_algHom_of_compatible_of_isAdicComplete [IsAdicComplete (Ideal.span {f}) C]
    (φ : ∀ n : ℕ, B →ₐ[A] C ⧸ Ideal.span {algebraMap A C f ^ (n + 1)})
    (hcompat : ∀ n, (quotFactorₐ (A := A) (span_pow_succ_succ_le (C := C) f n)).comp (φ (n + 1)) =
      φ n) :
    ∃ Φ : B →ₐ[A] C, ∀ n,
      (Ideal.Quotient.mkₐ A (Ideal.span {algebraMap A C f ^ (n + 1)})).comp Φ = φ n := by
  -- compatibility across several levels
  have hdown : ∀ m n (h : m ≤ n) (b : B),
      quotFactorₐ (A := A) (span_pow_succ_le_of_le (C := C) f h) (φ n b) = φ m b := by
    intro m n h b
    induction n, h using Nat.le_induction with
    | base => exact quotFactorₐ_self _
    | succ n hmn ih =>
      have h2 : quotFactorₐ (A := A) (span_pow_succ_succ_le (C := C) f n) (φ (n + 1) b) =
          φ n b := AlgHom.congr_fun (hcompat n) b
      calc quotFactorₐ (A := A) (span_pow_succ_le_of_le (C := C) f (Nat.le_succ_of_le hmn))
            (φ (n + 1) b)
          = quotFactorₐ (A := A) (span_pow_succ_le_of_le (C := C) f hmn)
              (quotFactorₐ (A := A) (span_pow_succ_succ_le (C := C) f n) (φ (n + 1) b)) := by
            obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (φ (n + 1) b)
            rw [← hc]
            rfl
        _ = φ m b := by rw [h2, ih]
  -- the limit of a compatible sequence
  have key : ∀ b : B, ∃! L : C, ∀ n,
      Ideal.Quotient.mk (Ideal.span {algebraMap A C f ^ (n + 1)}) L = φ n b := by
    intro b
    choose s hs using fun n ↦ Ideal.Quotient.mk_surjective (φ n b)
    have hsmod : ∀ m n (h : m ≤ n),
        Ideal.Quotient.mk (Ideal.span {algebraMap A C f ^ (m + 1)}) (s n) = φ m b := by
      intro m n h
      rw [← hdown m n h b, ← hs n, quotFactorₐ_mk]
    have hcauchy : ∀ {m n}, m ≤ n → s m ≡ s n [SMOD (Ideal.span {f} ^ m • ⊤ : Submodule A C)] := by
      intro m n h
      rw [SModEq.sub_mem, mem_span_pow_smul_top_iff]
      have h1 : Ideal.Quotient.mk (Ideal.span {algebraMap A C f ^ (m + 1)}) (s m) =
          Ideal.Quotient.mk (Ideal.span {algebraMap A C f ^ (m + 1)}) (s n) := by
        rw [hs m, hsmod m n h]
      rw [Ideal.Quotient.eq] at h1
      exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ m)) h1
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete (I := Ideal.span {f})
      (M := C)) hcauchy
    refine ⟨L, fun n ↦ ?_, fun L' hL' ↦ ?_⟩
    · have h1 := (hL (n + 1)).symm
      rw [SModEq.sub_mem, mem_span_pow_smul_top_iff] at h1
      rw [← hsmod n (n + 1) (Nat.le_succ n), Ideal.Quotient.eq]
      exact h1
    · apply sub_eq_zero.mp
      apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := Ideal.span {f}) (M := C))
      intro n
      rw [SModEq.zero, mem_span_pow_smul_top_iff]
      have h1 : Ideal.Quotient.mk (Ideal.span {algebraMap A C f ^ (n + 1)}) (L' - L) = 0 := by
        rw [map_sub, hL' n, ← hsmod n (n + 1) (Nat.le_succ n), sub_eq_zero]
        have h2 := (hL (n + 1)).symm
        rw [SModEq.sub_mem, mem_span_pow_smul_top_iff] at h2
        rw [Ideal.Quotient.eq]
        rw [← neg_sub]
        exact neg_mem h2
      rw [Ideal.Quotient.eq_zero_iff_mem] at h1
      exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ n)) h1
  choose Φ hΦ hΦuniq using key
  have hΦ' : ∀ (b : B) (L : C),
      (∀ n, Ideal.Quotient.mk (Ideal.span {algebraMap A C f ^ (n + 1)}) L = φ n b) → L = Φ b :=
    fun b L h ↦ hΦuniq b L h
  let Φ' : B →ₐ[A] C :=
    { toFun := Φ
      map_one' := by
        symm
        apply hΦ' 1 1
        intro n
        rw [map_one, map_one]
      map_mul' := fun b₁ b₂ ↦ by
        symm
        apply hΦ'
        intro n
        rw [map_mul, map_mul, hΦ b₁ n, hΦ b₂ n]
      map_zero' := by
        symm
        apply hΦ' 0 0
        intro n
        rw [map_zero, map_zero]
      map_add' := fun b₁ b₂ ↦ by
        symm
        apply hΦ'
        intro n
        rw [map_add, map_add, hΦ b₁ n, hΦ b₂ n]
      commutes' := fun _ ↦ by
        symm
        apply hΦ'
        intro n
        rw [AlgHom.commutes, Ideal.Quotient.mk_algebraMap] }
  refine ⟨Φ', fun n ↦ ?_⟩
  ext b
  exact hΦ b n

end Tower

/-! ### The main lifting theorem -/

section Main

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
variable {C : Type w} [CommRing C] [Algebra A C]

/-- **Formally étale lifting along a regular pair, complete case.**

Let `B`, `C` be `A`-algebras, `f x y ∈ A` with `C` `(f)`-adically complete.  Assume `B` is
formally étale over `A` after inverting `x`, after inverting `y`, formally unramified after
inverting `x * y`, that `x, y` is a regular pair on every `C / f^(n+1) C` and that `x` is regular
on `C / f C`.  Then every `A`-algebra map `B → C / f C` lifts to an `A`-algebra map `B → C`.

This is the algebraic heart of the complete-regular-local hypersurface lifting
(`Pcf.Stacks.Purity.HypersurfaceLiftingComplete`); its proof route (formal étaleness on two basic
opens, glued by a depth-two Hartogs argument, then completeness) replaces the local-cohomology
argument of Stacks Tags `0BM6`/`0EKS`. -/
theorem exists_algHom_lift_of_isAdicComplete (f : A) [IsAdicComplete (Ideal.span {f}) C]
    {x y : A}
    [Algebra.FormallyEtale A (Localization.Away (algebraMap A B x))]
    [Algebra.FormallyEtale A (Localization.Away (algebraMap A B y))]
    [Algebra.FormallyUnramified A (Localization.Away (algebraMap A B (x * y)))]
    (hx : ∀ n, IsSMulRegular (C ⧸ Ideal.span {algebraMap A C f ^ (n + 1)}) x)
    (hy : ∀ n, IsSMulRegular (C ⧸ Ideal.span {algebraMap A C f ^ (n + 1)}) y)
    (hxy : ∀ n, IsSMulRegular (QuotSMulTop x (C ⧸ Ideal.span {algebraMap A C f ^ (n + 1)})) y)
    (hxN : IsSMulRegular (C ⧸ Ideal.span {algebraMap A C f}) x)
    (φ₀ : B →ₐ[A] C ⧸ Ideal.span {algebraMap A C f}) :
    ∃ φ : B →ₐ[A] C, (Ideal.Quotient.mkₐ A (Ideal.span {algebraMap A C f})).comp φ = φ₀ := by
  let π : ∀ n : ℕ, (C ⧸ Ideal.span {algebraMap A C f ^ (n + 1)}) →ₐ[A]
      C ⧸ Ideal.span {algebraMap A C f} := fun n ↦ quotFactorₐ (span_pow_succ_le f)
  have hπsurj : ∀ n, Function.Surjective (π n) := fun n ↦ quotFactorₐ_surjective _
  have hπnil : ∀ n, IsNilpotent (RingHom.ker (π n)) := fun n ↦
    isNilpotent_ker_quotFactorₐ_span_pow f n
  -- the lifts at each level
  have hlift : ∀ n, ∃ φ : B →ₐ[A] C ⧸ Ideal.span {algebraMap A C f ^ (n + 1)},
      (π n).comp φ = φ₀ := fun n ↦
    exists_algHom_lift_of_regular_pair (π n) (hπsurj n) (hπnil n) (hx n) (hy n) (hxy n) hxN φ₀
  choose φ hφ using hlift
  -- compatibility by uniqueness
  have hcompat : ∀ n,
      (quotFactorₐ (A := A) (span_pow_succ_succ_le (C := C) f n)).comp (φ (n + 1)) = φ n := by
    intro n
    apply algHom_lift_unique_of_formallyUnramified (π n) (hπnil n) (hx n)
    rw [hφ n, ← AlgHom.comp_assoc]
    have : (π n).comp (quotFactorₐ (A := A) (span_pow_succ_succ_le (C := C) f n)) = π (n + 1) :=
      quotFactorₐ_comp_quotFactorₐ _ _
    rw [this, hφ (n + 1)]
  obtain ⟨Φ, hΦ⟩ := exists_algHom_of_compatible_of_isAdicComplete f φ hcompat
  refine ⟨Φ, ?_⟩
  have : (Ideal.Quotient.mkₐ A (Ideal.span {algebraMap A C f})) =
      (π 0).comp (Ideal.Quotient.mkₐ A (Ideal.span {algebraMap A C f ^ (0 + 1)})) := by
    ext c
    simp [π]
  rw [this, AlgHom.comp_assoc, hΦ 0, hφ 0]

end Main

#print axioms exists_algHom_of_regular_pair_of_agree
#print axioms algHom_lift_unique_of_formallyUnramified
#print axioms exists_algHom_lift_of_regular_pair
#print axioms exists_algHom_of_compatible_of_isAdicComplete
#print axioms exists_algHom_lift_of_isAdicComplete

end Pcf.Stacks
