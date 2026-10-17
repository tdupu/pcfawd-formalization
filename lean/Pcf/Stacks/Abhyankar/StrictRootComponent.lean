/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.StrictHeightOneTransport
public import Pcf.Stacks.Abhyankar.StrictNormalDecomposition
public import Pcf.Stacks.Purity.FiniteNormalModel

/-!
# Existence of the root-cover component (Stacks Tag `0EYG`, paragraph 4)

The normalization-existence part of paragraph 4.  In paragraph 4 of the proof
of Stacks Tag `0EYG` one forms the root cover `A' = A[x]/(x^E − a)` and `B' = B ⊗_A A'`, where
`B = N[1/a]` for a normal domain component `N`.  The structure `StrictRootComponentData` of
`StrictHeightOneTransport.lean` asks for a normal-domain component `N'` of the normalization of
`A'` in `B'`, with étaleness away from `x` and codimension-one unramifiedness (`0BRM`).  This file
constructs everything except the unramifiedness:

* `StrictRootComponentPreData A N a E`: all fields of `StrictRootComponentData` except
  `unramified`, plus the property `generic` (after inverting `x`, `N'` is generated over `A'` by
  the image of `N`), which identifies `N'[1/x]` with a domain factor of `B'`;
* `StrictRootComponentPreData.toData` (and `toDataOfRootMem`, which only needs unramifiedness at
  the height-one primes containing `x`): completing the pre-data with the `0BRM` input;
* `exists_strictRootComponentPreData`: existence for a Noetherian local `A`, `a ∈ 𝔪_A` a
  nonzerodivisor with `A ⧸ (a)` regular local, and `N` a finite domain, faithful over `A`, étale
  over `A` away from `a`.  The proof follows Stacks: `A'` is a regular local ring (`00NU`), hence
  normal; `B'` is étale over `A'` hence normal (`033C`), hence a finite product of normal domains
  (`030C`); `N'` is the integral closure of `A'` in a factor `B'_j`, finite because the generic
  fibre `Frac(A') ⊗ B'_j` is finite étale over `Frac(A')`;
* `PointedEtaleNeighborhood.strictBaseChangeFactor_faithfulSMul`: the domain factors
  `Nᵢ = StrictBaseChangeFactor R Ω S (e i)` of
  `localColimit_tensor_exists_normalDomain_decomposition` are faithful over
  `Rˢʰ = LocalColimit R Ω`;
* `PointedEtaleNeighborhood.exists_strictRootComponentPreData_strictBaseChangeFactor`: the
  existence statement for these factors over `Rˢʰ`.

## Assembly with the codimension-one input

Given `C : StrictRootComponentPreData A N a E` and a proof `hunr` that `C.carrier` is unramified
over `StrictRootCover a E` at all height-one primes (or only at those containing the root, via
`toDataOfRootMem`), `C.toData hunr : StrictRootComponentData A N a E` has carrier `C.carrier`
definitionally, so a purity hypothesis for `C.carrier` applies unchanged to
`exists_rootExponent_fractionRing_equiv_of_strictRootComponentData`.

Stacks Tag `03GE` (integral closure commutes with étale base change) is not needed: the
normalization is taken directly over `A'`.
-/

@[expose] public section

universe u

open IsLocalRing TensorProduct

namespace Pcf.Stacks

set_option linter.style.haveILetI false

section Normalization

variable {A' D : Type u} [CommRing A'] [CommRing D] [Algebra A' D]

/-- A domain that is faithful over a domain `A'` is torsion free, so it embeds into its generic
fibre `Frac(A') ⊗[A'] D`. -/
theorem injective_includeRight_fractionRing [IsDomain A'] [IsDomain D]
    [FaithfulSMul A' D] :
    Function.Injective (Algebra.TensorProduct.includeRight :
      D →ₐ[A'] FractionRing A' ⊗[A'] D) := by
  letI : Algebra D (FractionRing A' ⊗[A'] D) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid D (nonZeroDivisors A'))
      (FractionRing A' ⊗[A'] D) := inferInstance
  have h := IsLocalization.injective (M := Algebra.algebraMapSubmonoid D (nonZeroDivisors A'))
    (FractionRing A' ⊗[A'] D) (by
      rintro _ ⟨r, hr, rfl⟩
      apply mem_nonZeroDivisors_of_ne_zero
      intro h0
      apply nonZeroDivisors.ne_zero hr
      exact (FaithfulSMul.algebraMap_injective A' D) (by rw [h0, map_zero]))
  exact h

/-- **Finiteness of the normalization.**  The integral closure of a Noetherian normal domain `A'`
in an étale domain `D` is finite over `A'`: it embeds into the integral closure of `A'` in the
finite étale generic fibre `Frac(A') ⊗ D`, which is finite
(`finiteEtaleAlgebra_integralClosure_finite`; separability is automatic for étale algebras over a
field). -/
theorem integralClosure_finite_of_etale_of_isDomain [IsDomain A'] [IsIntegrallyClosed A']
    [IsNoetherianRing A'] [IsDomain D] [FaithfulSMul A' D] [Algebra.Etale A' D] :
    Module.Finite A' (integralClosure A' D) := by
  let K' := FractionRing A'
  let G := K' ⊗[A'] D
  have hfin := finiteEtaleAlgebra_integralClosure_finite A' K' G
  have heq : (Algebra.compHom G (algebraMap A' K') : Algebra A' G) =
      (inferInstance : Algebra A' G) :=
    Algebra.algebra_ext _ _ fun r ↦ rfl
  rw [heq] at hfin
  have hFG : (Subalgebra.toSubmodule (integralClosure A' G)).FG := Module.Finite.iff_fg.mp hfin
  have : IsNoetherian A' (Subalgebra.toSubmodule (integralClosure A' G)) :=
    isNoetherian_of_fg_of_noetherian _ hFG
  let g := (Algebra.TensorProduct.includeRight : D →ₐ[A'] G).toLinearMap
  let S := (Subalgebra.toSubmodule (integralClosure A' D)).map g
  have hle : S ≤ Subalgebra.toSubmodule (integralClosure A' G) := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hy : IsIntegral A' y).map Algebra.TensorProduct.includeRight
  have : IsNoetherian A' S := isNoetherian_of_le hle
  have hS : S.FG := Module.Finite.iff_fg.mp inferInstance
  exact Module.Finite.iff_fg.mpr
    (Submodule.fg_of_fg_map_injective g injective_includeRight_fractionRing hS)

/-- The integral closure of `A'` in an integrally closed domain `D` is integrally closed. -/
theorem integralClosure_isIntegrallyClosed [IsDomain D] [IsIntegrallyClosed D] :
    IsIntegrallyClosed (integralClosure A' D) :=
  IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn _ D

/-- The integral closure of `A'` in a faithful `A'`-algebra is faithful over `A'`. -/
theorem integralClosure_faithfulSMul [FaithfulSMul A' D] :
    FaithfulSMul A' (integralClosure A' D) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro r s h
  apply FaithfulSMul.algebraMap_injective A' D
  exact congrArg Subtype.val h

/-- If every element of `D` becomes integral over `A'` after multiplying by a power of `f`, and
`f` is a unit of `D`, then `D` is the localization of the integral closure of `A'` in `D` at
`f`. -/
theorem integralClosure_isLocalization_away (f : A') (hf : IsUnit (algebraMap A' D f))
    (hint : ∀ d : D, ∃ n : ℕ, IsIntegral A' (algebraMap A' D f ^ n * d)) :
    IsLocalization.Away (algebraMap A' (integralClosure A' D) f) D := by
  refine IsLocalization.Away.mk _ ?_ (fun d ↦ ?_) (fun y z h ↦ ⟨0, ?_⟩)
  · exact hf
  · obtain ⟨n, hn⟩ := hint d
    refine ⟨n, ⟨_, hn⟩, ?_⟩
    change d * (algebraMap A' D f) ^ n = algebraMap A' D f ^ n * d
    ring
  · rw [pow_zero, one_mul, one_mul]
    exact Subtype.ext h

/-- Étaleness away from `f`: if the localization of `C` at `f` is étale over `A'`, then `C` is
étale over `A'` at every prime not containing `f`. -/
theorem isEtaleAt_of_isLocalization_away {C : Type u} [CommRing C] [Algebra A' C] [Algebra C D]
    [IsScalarTower A' C D] (f : C) [IsLocalization.Away f D] [Algebra.Etale A' D]
    (w : PrimeSpectrum C) (hw : f ∉ w.asIdeal) : Algebra.IsEtaleAt A' w.asIdeal := by
  let e : Localization.Away f ≃ₐ[A'] D :=
    (IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) D).restrictScalars A'
  have : Algebra.FormallyEtale A' (Localization.Away f) := Algebra.FormallyEtale.of_equiv e.symm
  exact Algebra.basicOpen_subset_etaleLocus_iff.mpr this hw

end Normalization

section ComponentPreData

variable (A N : Type u) [CommRing A] [CommRing N] [Algebra A N] (a : A) (E : ℕ)

/-- **The root-cover component without the codimension-one input.**  All the data of
`StrictRootComponentData A N a E` except the field `unramified`, together with the property
`generic` that pins the component down: after inverting the root `x`, every element of `N'` lies
in the `A'`-subalgebra generated by the image of `N`, i.e. the map `A' ⊗_A N → N'` becomes
surjective after inverting `x` (so `N'[1/x]` is a domain factor of `(A' ⊗_A N)[1/x]`, the ring
`B'` of the proof of Stacks `0EYG`, and `N'` is the normalization of `A'` in it).

It is produced by `exists_strictRootComponentPreData`; adding the codimension-one `0BRM`
conclusion with `StrictRootComponentPreData.toData` gives `StrictRootComponentData`. -/
structure StrictRootComponentPreData where
  /-- The component `N'`. -/
  carrier : Type u
  [commRing : CommRing carrier]
  [algebraRoot : Algebra (StrictRootCover a E) carrier]
  [algebraBase : Algebra A carrier]
  [towerRoot : IsScalarTower A (StrictRootCover a E) carrier]
  [algebraComponent : Algebra N carrier]
  [towerComponent : IsScalarTower A N carrier]
  [isDomain : IsDomain carrier]
  [isIntegrallyClosed : IsIntegrallyClosed carrier]
  [finite : Module.Finite (StrictRootCover a E) carrier]
  [faithfulSMul : FaithfulSMul (StrictRootCover a E) carrier]
  /-- `N'` is étale over `A'` away from the root. -/
  etaleAway : ∀ w : PrimeSpectrum carrier,
    algebraMap (StrictRootCover a E) carrier (strictRoot a E) ∉ w.asIdeal →
      Algebra.IsEtaleAt (StrictRootCover a E) w.asIdeal
  /-- After inverting the root, `N'` is generated over `A'` by the image of `N`. -/
  generic : ∀ y : carrier, ∃ k : ℕ,
    algebraMap (StrictRootCover a E) carrier (strictRoot a E) ^ k * y ∈
      Algebra.adjoin (StrictRootCover a E) (Set.range (algebraMap N carrier))

attribute [instance] StrictRootComponentPreData.commRing StrictRootComponentPreData.algebraRoot
  StrictRootComponentPreData.algebraBase StrictRootComponentPreData.towerRoot
  StrictRootComponentPreData.algebraComponent StrictRootComponentPreData.towerComponent
  StrictRootComponentPreData.isDomain StrictRootComponentPreData.isIntegrallyClosed
  StrictRootComponentPreData.finite StrictRootComponentPreData.faithfulSMul

variable {A N a E}

/-- Completing the pre-data with the codimension-one unramifiedness (Stacks `0BRM`) gives the
component data consumed by
`exists_rootExponent_fractionRing_equiv_of_strictRootComponentData`.  The carrier is
unchanged (`StrictRootComponentPreData.toData_carrier`). -/
def StrictRootComponentPreData.toData (C : StrictRootComponentPreData A N a E)
    (hunramified : ∀ w : PrimeSpectrum C.carrier, w.asIdeal.height = 1 →
      Algebra.IsUnramifiedAt (StrictRootCover a E) w.asIdeal) :
    StrictRootComponentData A N a E where
  carrier := C.carrier
  etaleAway := C.etaleAway
  unramified := hunramified

@[simp]
theorem StrictRootComponentPreData.toData_carrier (C : StrictRootComponentPreData A N a E)
    (hunramified : ∀ w : PrimeSpectrum C.carrier, w.asIdeal.height = 1 →
      Algebra.IsUnramifiedAt (StrictRootCover a E) w.asIdeal) :
    (C.toData hunramified).carrier = C.carrier :=
  rfl

/-- Variant of `toData` where unramifiedness is only supplied at the height-one primes containing
the root (away from the root it follows from `etaleAway`). -/
def StrictRootComponentPreData.toDataOfRootMem (C : StrictRootComponentPreData A N a E)
    (hroot : ∀ w : PrimeSpectrum C.carrier, w.asIdeal.height = 1 →
      algebraMap (StrictRootCover a E) C.carrier (strictRoot a E) ∈ w.asIdeal →
        Algebra.IsUnramifiedAt (StrictRootCover a E) w.asIdeal) :
    StrictRootComponentData A N a E :=
  C.toData (forall_height_one_isUnramifiedAt_of_root_mem _ C.etaleAway hroot)

end ComponentPreData

section Construction

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  {N : Type u} [CommRing N] [Algebra A N] [Module.Finite A N] {a : A} {E : ℕ}

omit [IsNoetherianRing A] [IsLocalRing A] [Module.Finite A N] in
/-- `(A' ⊗_A N)[1/a]` is nonzero when `N` is a domain faithful over `A` and `a ≠ 0`: it maps to
an algebraic closure of `Frac(N)`, sending `x` to an `E`-th root of `a`. -/
theorem strictRootCover_tensor_away_nontrivial (hE : 1 ≤ E) [IsDomain N] [FaithfulSMul A N]
    (ha0 : a ≠ 0) :
    Nontrivial (Localization.Away (algebraMap (StrictRootCover a E)
      (StrictRootCover a E ⊗[A] N) (algebraMap A (StrictRootCover a E) a))) := by
  let L := AlgebraicClosure (FractionRing N)
  have hφ : Function.Injective (algebraMap N L) := by
    rw [IsScalarTower.algebraMap_eq N (FractionRing N) L]
    exact (algebraMap (FractionRing N) L).injective.comp (IsFractionRing.injective N _)
  have haL : algebraMap A L a ≠ 0 := by
    intro h
    apply ha0
    apply FaithfulSMul.algebraMap_injective A N
    apply hφ
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, h, map_zero]
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A L a) (by omega : 0 < E)
  let ψ : StrictRootCover a E →ₐ[A] L :=
    AdjoinRoot.liftAlgHom (Pcf.LocalModel.localPoly (1 : Aˣ) a E) (Algebra.ofId A L) r (by
      simp only [Pcf.LocalModel.localPoly, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
        Polynomial.eval₂_C, Units.val_one, one_mul]
      rw [hr]
      exact sub_eq_zero.mpr rfl)
  let F : StrictRootCover a E ⊗[A] N →ₐ[A] L :=
    Algebra.TensorProduct.lift ψ (IsScalarTower.toAlgHom A N L) fun _ _ ↦ Commute.all _ _
  have hunit : IsUnit (F.toRingHom (algebraMap (StrictRootCover a E)
      (StrictRootCover a E ⊗[A] N) (algebraMap A (StrictRootCover a E) a))) := by
    change IsUnit (F (algebraMap A (StrictRootCover a E) a ⊗ₜ[A] (1 : N)))
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one, ψ.commutes]
    exact (IsUnit.mk0 _ haL)
  exact (IsLocalization.Away.lift _ hunit).domain_nontrivial

/-- **The component over a domain factor.**  Let `B'_j` be an étale domain over the root cover
`A'`, receiving `A' ⊗_A N` by `θ`, in which `a` is a unit and which is generated by the image of
`θ` after inverting `a`.  Then the integral closure `N'` of `A'` in `B'_j` carries the root-cover
component pre-data: it is finite (`integralClosure_finite_of_etale_of_isDomain`), an integrally
closed domain (`033C` for `B'_j`, then `integralClosure_isIntegrallyClosed`), faithful, and
`N'[1/a] = B'_j` (`integralClosure_isLocalization_away`), so `N'` is étale over `A'` away from
`a`, equivalently away from the root `x`, since `x^E = a`. -/
theorem nonempty_strictRootComponentPreData_of_factor (ha : a ∈ maximalIdeal A)
    (ha0 : a ∈ nonZeroDivisors A) [IsRegularLocalRing (A ⧸ Ideal.span ({a} : Set A))]
    (hE : 1 ≤ E) {Bj : Type u} [CommRing Bj] [Algebra (StrictRootCover a E) Bj] [IsDomain Bj]
    [Algebra.Etale (StrictRootCover a E) Bj]
    (θ : StrictRootCover a E ⊗[A] N →ₐ[StrictRootCover a E] Bj)
    (hunit : IsUnit (algebraMap (StrictRootCover a E) Bj (algebraMap A (StrictRootCover a E) a)))
    (hsurj : ∀ d : Bj, ∃ n : ℕ, ∃ t : StrictRootCover a E ⊗[A] N,
      algebraMap (StrictRootCover a E) Bj (algebraMap A (StrictRootCover a E) a) ^ n * d = θ t) :
    Nonempty (StrictRootComponentPreData A N a E) := by
  let A' := StrictRootCover a E
  let x : A' := strictRoot a E
  let a' : A' := algebraMap A A' a
  let P := A' ⊗[A] N
  letI : IsNoetherianRing A' := strictRootCover_isNoetherianRing a hE
  letI : IsDomain A' := strictRootCover_isDomain a ha hE ha0
  letI : IsIntegrallyClosed A' := strictRootCover_isIntegrallyClosed a ha hE ha0
  letI : Algebra A Bj := Algebra.compHom Bj (algebraMap A A')
  haveI : IsScalarTower A A' Bj := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsIntegrallyClosed Bj := isIntegrallyClosed_of_etale A' Bj
  haveI : FaithfulSMul A' Bj := faithfulSMul_of_flat_of_isDomain A' Bj
  let C := integralClosure A' Bj
  haveI : Module.Finite A' C := integralClosure_finite_of_etale_of_isDomain
  haveI : IsIntegrallyClosed C := integralClosure_isIntegrallyClosed
  haveI : FaithfulSMul A' C := integralClosure_faithfulSMul
  haveI : Algebra.IsIntegral A N := Algebra.IsIntegral.of_finite A N
  haveI : Algebra.IsIntegral A' P := Algebra.IsIntegral.tensorProduct A A' N
  have hθint : ∀ t : P, IsIntegral A' (θ t) := fun t ↦ (Algebra.IsIntegral.isIntegral t).map θ
  haveI hloc : IsLocalization.Away (algebraMap A' C a') Bj :=
    integralClosure_isLocalization_away a' hunit fun d ↦ by
      obtain ⟨n, t, h⟩ := hsurj d
      exact ⟨n, h ▸ hθint t⟩
  -- the map `N → N'`
  let g : N →ₐ[A] Bj := (θ.restrictScalars A).comp Algebra.TensorProduct.includeRight
  have hg : ∀ n, g n ∈ C := fun n ↦
    ((Algebra.IsIntegral.isIntegral (R := A) n).map g).tower_top
  let φ : N →+* C := g.toRingHom.codRestrict C hg
  letI : Algebra N C := φ.toAlgebra
  haveI : IsScalarTower A N C := IsScalarTower.of_algebraMap_eq fun r ↦
    Subtype.ext (g.commutes r).symm
  -- the root and the divisor
  have hax : algebraMap A' C a' = algebraMap A' C x ^ E := by
    rw [← map_pow, strictRoot_pow]
  have hgen : ∀ t : P, ∃ c ∈ Algebra.adjoin A' (Set.range (algebraMap N C)), (c : Bj) = θ t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul r n =>
      refine ⟨algebraMap A' C r * algebraMap N C n, Subalgebra.mul_mem _
        (Subalgebra.algebraMap_mem _ r) (Algebra.subset_adjoin ⟨n, rfl⟩), ?_⟩
      have : r ⊗ₜ[A] n = algebraMap A' P r * Algebra.TensorProduct.includeRight n := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rfl
      rw [this, map_mul, θ.commutes]
      rfl
    | add t₁ t₂ h₁ h₂ =>
      obtain ⟨c₁, hc₁, e₁⟩ := h₁
      obtain ⟨c₂, hc₂, e₂⟩ := h₂
      exact ⟨c₁ + c₂, add_mem hc₁ hc₂, by rw [map_add, ← e₁, ← e₂]; rfl⟩
  have hgenC : ∀ y : C, ∃ k : ℕ,
      algebraMap A' C x ^ k * y ∈ Algebra.adjoin A' (Set.range (algebraMap N C)) := by
    intro y
    obtain ⟨n, t, h⟩ := hsurj y.1
    obtain ⟨c, hc, hct⟩ := hgen t
    refine ⟨E * n, ?_⟩
    have : algebraMap A' C x ^ (E * n) * y = c := by
      rw [pow_mul, ← hax]
      apply Subtype.ext
      change algebraMap A' Bj a' ^ n * y.1 = c.1
      rw [hct, h]
    rw [this]
    exact hc
  have hetC : ∀ w : PrimeSpectrum C, algebraMap A' C x ∉ w.asIdeal →
      Algebra.IsEtaleAt A' w.asIdeal := by
    intro w hw
    refine isEtaleAt_of_isLocalization_away (D := Bj) (algebraMap A' C a') w fun h ↦ hw ?_
    rw [hax] at h
    exact w.isPrime.mem_of_pow_mem E h
  exact ⟨{ carrier := C, etaleAway := hetC, generic := hgenC }⟩

/-- **Existence of the root-cover component (Stacks `0EYG`, paragraph 4).**  Let `A` be a
Noetherian local ring, `a ∈ 𝔪_A` a nonzerodivisor with `A ⧸ (a)` regular local, `E ≥ 1`, and
`N` a finite `A`-algebra which is a domain, faithful over `A`, and étale over `A` away from `a`.
Then there is a normal-domain component `N'` of the normalization of the root cover
`A' = A[x]/(x^E − a)` in `B' = (A' ⊗_A N)[1/x]`, with all the data of
`StrictRootComponentData` except codimension-one unramifiedness.

Proof, following the proof of Stacks `0EYG`: `A'` is regular local (`00NU`), hence a Noetherian
normal domain; `B'` is étale over `A'` (`etale_localizationAway_baseChange`), hence a Noetherian
normal ring (`033C`, `IsStacksNormalRing.of_etale`), hence a finite product of normal domains
(`030C`, `IsStacksNormalRing.exists_completeOrthogonalIdempotents`); `B'` is nonzero
(`strictRootCover_tensor_away_nontrivial`), so some factor `B'_j` exists.  It is a localization of
`B'`, hence étale over `A'`, and it is a domain, hence faithful over `A'`
(`faithfulSMul_of_flat_of_isDomain`).  Take `N'` the integral closure of `A'` in `B'_j`: it is
finite (`integralClosure_finite_of_etale_of_isDomain`, via the finite étale generic fibre), an
integrally closed domain, `N'[1/a] = B'_j` (elements of `A' ⊗_A N` are integral over `A'`), so
`N'` is étale over `A'` away from `a`, equivalently away from `x` since `x^E = a`.

Divergence from Stacks: Stacks works with `B' = B ⊗_A A'` for the domain `B = N[1/a]` and does not
take a normalization (it passes directly to `0EYE`); the normalization `N'` is the finite normal
model required by pcf's form of `0EYE`. -/
theorem exists_strictRootComponentPreData (ha : a ∈ maximalIdeal A)
    (ha0 : a ∈ nonZeroDivisors A) [IsRegularLocalRing (A ⧸ Ideal.span ({a} : Set A))]
    (hE : 1 ≤ E) [IsDomain N] [FaithfulSMul A N]
    (hetale : ∀ w : PrimeSpectrum N, algebraMap A N a ∉ w.asIdeal →
      Algebra.IsEtaleAt A w.asIdeal) :
    Nonempty (StrictRootComponentPreData A N a E) := by
  let A' := StrictRootCover a E
  let a' : A' := algebraMap A A' a
  letI : IsNoetherianRing A' := strictRootCover_isNoetherianRing a hE
  letI : IsRegularLocalRing A' := strictRootCover_isRegularLocalRing a ha hE ha0
  let P := A' ⊗[A] N
  let B := Localization.Away (algebraMap A' P a')
  haveI : Algebra.Etale A' B :=
    PointedEtaleNeighborhood.etale_localizationAway_baseChange A' a hetale
  haveI : Nontrivial B := strictRootCover_tensor_away_nontrivial hE (nonZeroDivisors.ne_zero ha0)
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A' B
  have hA'n : IsStacksNormalRing A' := by
    haveI := isRegularRing_of_isRegularLocalRing A'
    exact isStacksNormalRing_of_isRegularRing A'
  have hBn : IsStacksNormalRing B := IsStacksNormalRing.of_etale B hA'n
  obtain ⟨ι, _, ε, hε, hεi⟩ := hBn.exists_completeOrthogonalIdempotents
  obtain ⟨j⟩ : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hε.complete
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    exact zero_ne_one this
  let Bj := B ⧸ Ideal.span {1 - ε j}
  haveI : (Ideal.span {1 - ε j}).IsPrime := (hεi j).1
  haveI : IsDomain Bj := Ideal.Quotient.isDomain _
  haveI : IsLocalization.Away (ε j) Bj :=
    IsLocalization.Away.quotient_of_isIdempotentElem (hε.idem j)
  haveI : Algebra.Etale B Bj := Algebra.Etale.of_equiv
    (IsLocalization.algEquiv (Submonoid.powers (ε j)) (Localization.Away (ε j)) Bj)
  haveI : Algebra.Etale A' Bj := Algebra.Etale.comp A' B Bj
  -- the map `A' ⊗_A N → B'_j`
  let θ : P →ₐ[A'] Bj := (IsScalarTower.toAlgHom A' B Bj).comp (IsScalarTower.toAlgHom A' P B)
  have haBj : algebraMap A' Bj a' =
      Ideal.Quotient.mk (Ideal.span {1 - ε j}) (algebraMap P B (algebraMap A' P a')) := by
    rw [← IsScalarTower.algebraMap_apply]
    rfl
  refine nonempty_strictRootComponentPreData_of_factor ha ha0 hE θ ?_ fun d ↦ ?_
  · rw [haBj]
    exact (IsLocalization.Away.algebraMap_isUnit _).map _
  · obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective d
    obtain ⟨n, t, ht⟩ := IsLocalization.Away.surj (algebraMap A' P a') b
    refine ⟨n, t, ?_⟩
    change _ = Ideal.Quotient.mk (Ideal.span {1 - ε j}) (algebraMap P B t)
    rw [haBj, ← ht, ← map_pow, ← map_mul, mul_comm]

end Construction

section IdempotentFactor

variable {Rb P : Type*} [CommRing Rb] [CommRing P] [Algebra Rb P] (f : P) {e : P}

/-- If `P[1/f]` is étale over `Rb` and `e` is an idempotent of `P`, then the factor
`(P ⧸ (1 - e))[1/f]` is étale over `Rb`: it is the localization of `P[1/f]` at `e`. -/
theorem etale_localizationAway_quotient_idempotent (he : IsIdempotentElem e)
    [Algebra.Etale Rb (Localization.Away f)] :
    Algebra.Etale Rb (Localization.Away (Ideal.Quotient.mk (Ideal.span {1 - e}) f)) := by
  let Nf := P ⧸ Ideal.span {1 - e}
  let fN : Nf := Ideal.Quotient.mk (Ideal.span {1 - e}) f
  let B := Localization.Away f
  let T := Localization.Away fN
  haveI : IsLocalization.Away e Nf := IsLocalization.Away.quotient_of_isIdempotentElem he
  haveI : IsLocalization.Away (algebraMap P Nf f) T := Localization.isLocalization
  have hu : IsUnit (((algebraMap Nf T).comp (algebraMap P Nf)) f) :=
    IsLocalization.Away.algebraMap_isUnit fN
  letI : Algebra B T := (IsLocalization.Away.lift f hu).toAlgebra
  haveI : IsScalarTower P B T := IsScalarTower.of_algebraMap_eq fun p ↦
    (IsLocalization.Away.lift_eq f hu p).symm
  haveI : IsScalarTower P Nf T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsLocalization.Away (algebraMap P B e) T := IsLocalization.Away.commutes B Nf T f e
  haveI : Algebra.Etale B T := Algebra.Etale.of_equiv
    (IsLocalization.algEquiv (Submonoid.powers (algebraMap P B e))
      (Localization.Away (algebraMap P B e)) T)
  haveI : IsScalarTower Rb P T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower Rb B T := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply Rb P B, ← IsScalarTower.algebraMap_apply P B T,
      ← IsScalarTower.algebraMap_apply]
  exact Algebra.Etale.comp Rb B T

/-- The factor `P ⧸ (1 - e)` is étale over `Rb` at every prime not containing `f`. -/
theorem isEtaleAt_quotient_idempotent (he : IsIdempotentElem e)
    [Algebra.Etale Rb (Localization.Away f)] (w : PrimeSpectrum (P ⧸ Ideal.span {1 - e}))
    (hw : Ideal.Quotient.mk (Ideal.span {1 - e}) f ∉ w.asIdeal) :
    Algebra.IsEtaleAt Rb w.asIdeal := by
  haveI := etale_localizationAway_quotient_idempotent (Rb := Rb) f he
  exact Algebra.basicOpen_subset_etaleLocus_iff.mpr inferInstance hw

/-- A domain factor `P ⧸ (1 - e)` embedding into its localization at `f` is faithful over a
domain `Rb` when `P[1/f]` is étale over `Rb`: the localized factor is étale, hence flat, and
nonzero (`faithfulSMul_of_flat_of_isDomain`). -/
theorem faithfulSMul_quotient_idempotent [IsDomain Rb] (he : IsIdempotentElem e)
    [Algebra.Etale Rb (Localization.Away f)] [IsDomain (P ⧸ Ideal.span {1 - e})]
    (hinj : Function.Injective (algebraMap (P ⧸ Ideal.span {1 - e})
      (Localization.Away (Ideal.Quotient.mk (Ideal.span {1 - e}) f)))) :
    FaithfulSMul Rb (P ⧸ Ideal.span {1 - e}) := by
  let T := Localization.Away (Ideal.Quotient.mk (Ideal.span {1 - e}) f)
  haveI := etale_localizationAway_quotient_idempotent (Rb := Rb) f he
  haveI : Nontrivial T := hinj.nontrivial
  haveI : FaithfulSMul Rb T := faithfulSMul_of_flat_of_isDomain Rb T
  rw [faithfulSMul_iff_algebraMap_injective]
  intro r s h
  apply FaithfulSMul.algebraMap_injective Rb T
  rw [IsScalarTower.algebraMap_apply Rb (P ⧸ Ideal.span {1 - e}) T,
    IsScalarTower.algebraMap_apply Rb (P ⧸ Ideal.span {1 - e}) T s, h]

end IdempotentFactor

namespace PointedEtaleNeighborhood

variable {R Ω S : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Field Ω]
  [Algebra R Ω] [Algebra (ResidueField R) Ω] [IsScalarTower R (ResidueField R) Ω]
  [IsSepClosure (ResidueField R) Ω] [CommRing S] [Algebra R S] [Module.Finite R S]

/-- **Faithfulness of the normal-domain factors.**  A domain factor `Nᵢ` of `Rˢʰ ⊗[R] S` that is the
integral closure of `Rˢʰ` in `Nᵢ[1/a]` is faithful over `Rˢʰ`: `Nᵢ[1/a]` is a localization of the
étale `Rˢʰ`-algebra `(Rˢʰ ⊗[R] S)[1/a]`, hence flat, and nonzero, over the domain `Rˢʰ`
(`faithfulSMul_of_flat_of_isDomain`); and `Nᵢ ⊂ Nᵢ[1/a]`. -/
theorem strictBaseChangeFactor_faithfulSMul (a : R) (ha : a ∈ maximalIdeal R)
    (hreg : a ∈ nonZeroDivisors R) [IsRegularLocalRing (R ⧸ Ideal.span {a})]
    (hetale : ∀ w : PrimeSpectrum S, algebraMap R S a ∉ w.asIdeal →
      Algebra.IsEtaleAt R w.asIdeal)
    {e : StrictBaseChange R Ω S} (he : IsIdempotentElem e)
    [IsDomain (StrictBaseChangeFactor R Ω S e)]
    [hic : IsIntegralClosure (StrictBaseChangeFactor R Ω S e) (LocalColimit R Ω)
      (StrictBaseChangeFactorAway Ω S a e)] :
    FaithfulSMul (LocalColimit R Ω) (StrictBaseChangeFactor R Ω S e) := by
  haveI : IsRegularLocalRing R := Pcf.isRegularLocalRing_of_quotient_nonZeroDivisor a ha hreg
  haveI : IsRegularLocalRing (LocalColimit R Ω) := localColimit_isRegularLocalRing
  haveI : IsDomain (LocalColimit R Ω) := isDomain_of_isRegularLocalRing _
  haveI := etale_localizationAway_baseChange (S := S) (LocalColimit R Ω) a hetale
  exact faithfulSMul_quotient_idempotent _ he hic.algebraMap_injective

/-- **Existence of the root-cover component for the normal-domain factors.**  For a factor
`Nᵢ = StrictBaseChangeFactor R Ω S (e i)` from
`localColimit_tensor_exists_normalDomain_decomposition` (a domain, finite over `Rˢʰ`, the
integral closure of `Rˢʰ` in `Nᵢ[1/a]`), the root-cover component pre-data over `Rˢʰ` exists
for every `E ≥ 1`. -/
theorem exists_strictRootComponentPreData_strictBaseChangeFactor (a : R)
    (ha : a ∈ maximalIdeal R) (hreg : a ∈ nonZeroDivisors R)
    [IsRegularLocalRing (R ⧸ Ideal.span {a})]
    (hetale : ∀ w : PrimeSpectrum S, algebraMap R S a ∉ w.asIdeal →
      Algebra.IsEtaleAt R w.asIdeal)
    {e : StrictBaseChange R Ω S} (he : IsIdempotentElem e)
    [IsDomain (StrictBaseChangeFactor R Ω S e)]
    [Module.Finite (LocalColimit R Ω) (StrictBaseChangeFactor R Ω S e)]
    [IsIntegralClosure (StrictBaseChangeFactor R Ω S e) (LocalColimit R Ω)
      (StrictBaseChangeFactorAway Ω S a e)]
    (E : ℕ) (hE : 1 ≤ E) :
    Nonempty (StrictRootComponentPreData (LocalColimit R Ω) (StrictBaseChangeFactor R Ω S e)
      (algebraMap R (LocalColimit R Ω) a) E) := by
  haveI := strictBaseChangeFactor_faithfulSMul a ha hreg hetale he
  haveI : IsRegularLocalRing (LocalColimit R Ω ⧸
      Ideal.span ({algebraMap R (LocalColimit R Ω) a} : Set (LocalColimit R Ω))) :=
    quotient_span_localColimit_isRegularLocalRing (Ω := Ω) a
  have ha' : algebraMap R (LocalColimit R Ω) a ∈ maximalIdeal (LocalColimit R Ω) :=
    map_le_maximalIdeal_localColimit (Ideal.span {a})
      (by rw [Ideal.span_le, Set.singleton_subset_iff]; exact ha)
      (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_singleton a)))
  have ha0' : algebraMap R (LocalColimit R Ω) a ∈ nonZeroDivisors (LocalColimit R Ω) :=
    algebraMap_mem_nonZeroDivisors_localColimit hreg
  haveI := etale_localizationAway_baseChange (S := S) (LocalColimit R Ω) a hetale
  exact exists_strictRootComponentPreData ha' ha0' hE fun w hw ↦
    isEtaleAt_quotient_idempotent _ he w hw

end PointedEtaleNeighborhood

#print axioms injective_includeRight_fractionRing
#print axioms integralClosure_finite_of_etale_of_isDomain
#print axioms integralClosure_isIntegrallyClosed
#print axioms integralClosure_faithfulSMul
#print axioms integralClosure_isLocalization_away
#print axioms isEtaleAt_of_isLocalization_away
#print axioms StrictRootComponentPreData.toData
#print axioms StrictRootComponentPreData.toDataOfRootMem
#print axioms etale_localizationAway_quotient_idempotent
#print axioms isEtaleAt_quotient_idempotent
#print axioms faithfulSMul_quotient_idempotent
#print axioms strictRootCover_tensor_away_nontrivial
#print axioms nonempty_strictRootComponentPreData_of_factor
#print axioms exists_strictRootComponentPreData
#print axioms PointedEtaleNeighborhood.strictBaseChangeFactor_faithfulSMul
#print axioms PointedEtaleNeighborhood.exists_strictRootComponentPreData_strictBaseChangeFactor

end Pcf.Stacks
