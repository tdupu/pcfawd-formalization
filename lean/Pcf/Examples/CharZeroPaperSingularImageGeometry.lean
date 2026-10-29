/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.CharZeroPaperSingularImage
public import Pcf.Examples.CharZeroPaperCuspBranch
public import Pcf.Examples.CharZeroPaperConeBranch
public import Pcf.Examples.CharZeroPaperCuspCanonical
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Unramified.Locus
public import Pcf.Bounding.ReducedFiberBranch

/-!
# Scheme geometry of the singular-image-divisor example

For `latex/paper.tex`, Example `ex:branch-sing-B`, this file constructs the
actual scheme morphism `f = (F,G) : 𝔸² → 𝔸²` and proves it finite and
surjective. The algebraic independence of `F,G` is derived from integrality
of `k[x,y]` over `k[F,G]` and transcendence degree, not assumed.

The cusp `B = V(U³-12aV²)` is an integral closed subscheme. For nonzero
`α,β` with `α³ = 12aβ²` its coordinate ring is identified with `k[s²,s³]`
through `s ↦ (αs², βs³)`; via `CharZeroPaperCuspCanonical`, `Spec k[s]` is the
canonical normalization of `B`. On each critical line `y = λx` the restriction
of `f` is the unique factorization through `B`; its canonical normalized lift is
`t ↦ t²`, and its canonical normalized branch support is the origin of `B`.

Each critical line has ramification index three over `B`; the Jacobian `4H²`
gives unramifiedness at every other height-one prime, so the reduced-fiber
branch locus of `f` is exactly `B` and `Z = ∅`. The plane is smooth and the
origin of `B` is a non-regular point, so the `Sing(B)` term is needed.
-/

@[expose] public section
noncomputable section

namespace Pcf.Examples.CharZeroPaperSingularImageGeometry

open CategoryTheory AlgebraicGeometry MvPolynomial
open CharZeroPaperSingularImage Pcf.PaperCharZero

universe u
variable {K : Type u} [Field K]

/-! ### The finite surjective map `f = (F,G)` -/

/-- The pullback `U ↦ F, V ↦ G` of the plane map `f`. -/
def mapPullback (a : K) : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K :=
  aeval ![F (C a) (X 0) (X 1), G (X 0) (X 1)]

@[simp] theorem mapPullback_X_zero (a : K) : mapPullback a (X 0) = F (C a) (X 0) (X 1) := by
  simp [mapPullback]

@[simp] theorem mapPullback_X_one (a : K) :
    mapPullback a (X 1) = G (X 0) (X 1 : MvPolynomial (Fin 2) K) := by
  simp [mapPullback]

theorem mapPullback_range (a : K) : (mapPullback a).range = coordinateSubalgebra a := by
  rw [mapPullback, ← Algebra.adjoin_range_eq_range_aeval]
  unfold coordinateSubalgebra
  congr 1
  ext p
  simp [or_comm]

/-- `F` and `G` are algebraically independent: `k[x,y]` is integral over `k[F,G]`
and has transcendence degree two. -/
theorem mapPullback_injective [CharZero K] (a : K) (ha : a ^ 2 = -3) :
    Function.Injective (mapPullback a) := by
  let x : Fin 2 → MvPolynomial (Fin 2) K := ![F (C a) (X 0) (X 1), G (X 0) (X 1)]
  have hs : Set.range x = {F (C a) (X 0) (X 1), G (X 0) (X 1)} := by
    ext p
    simp [x, or_comm]
  have : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range x)) (MvPolynomial (Fin 2) K) := by
    rw [hs]
    have : Algebra.IsIntegral (coordinateSubalgebra a) (MvPolynomial (Fin 2) K) :=
      ⟨source_polynomial_isIntegral a ha⟩
    exact Algebra.IsIntegral.isAlgebraic (R := coordinateSubalgebra a)
      (A := MvPolynomial (Fin 2) K)
  have hle : Cardinal.lift.{u} (Cardinal.mk (Fin 2)) ≤
      Cardinal.lift.{0} (Algebra.trdeg K (MvPolynomial (Fin 2) K)) := by
    rw [MvPolynomial.trdeg_of_isDomain]
    simp
  have hb : IsTranscendenceBasis K x :=
    Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite (R := K) x hle
  exact hb.1

theorem mapPullback_finite [CharZero K] (a : K) (ha : a ^ 2 = -3) :
    (mapPullback a).toRingHom.Finite := by
  have h1 : (algebraMap (coordinateSubalgebra a) (MvPolynomial (Fin 2) K)).Finite :=
    RingHom.finite_algebraMap.mpr (coordinateSubalgebra_finite a ha)
  let r : MvPolynomial (Fin 2) K →+* coordinateSubalgebra a :=
    (mapPullback a).toRingHom.codRestrict (coordinateSubalgebra a).toSubring (fun p => by
      rw [← mapPullback_range]
      exact (mapPullback a).mem_range_self p)
  have hr : Function.Surjective r := by
    intro q
    have hq : q.1 ∈ (mapPullback a).range := by
      rw [mapPullback_range]
      exact q.2
    obtain ⟨p, hp⟩ := hq
    exact ⟨p, Subtype.ext hp⟩
  exact h1.comp (RingHom.Finite.of_surjective r hr)

abbrev plane (K : Type u) [Field K] : Scheme := Spec (.of (MvPolynomial (Fin 2) K))
abbrev line (K : Type u) [Field K] : Scheme := Spec (.of (Polynomial K))

/-- The actual scheme morphism `f = (F,G) : 𝔸² → 𝔸²`. -/
def planeMap (a : K) : plane K ⟶ plane K :=
  Spec.map (CommRingCat.ofHom (mapPullback a).toRingHom)

theorem planeMap_isFinite [CharZero K] (a : K) (ha : a ^ 2 = -3) : IsFinite (planeMap a) :=
  (IsFinite.SpecMap_iff _).mpr (mapPullback_finite a ha)

/-- `ex:branch-sing-B`: `f` is finite and surjective. -/
theorem planeMap_surjective [CharZero K] (a : K) (ha : a ^ 2 = -3) : Surjective (planeMap a) :=
  ⟨(mapPullback_finite a ha).to_isIntegral.comap_surjective (mapPullback_injective a ha)⟩

/-! ### The cusp `B` -/

/-- The cusp equation `U³ - 12aV²`. -/
def cuspEquation (a : K) : MvPolynomial (Fin 2) K := X 0 ^ 3 - C (12 * a) * X 1 ^ 2

theorem C_sq_eq (a : K) (ha : a ^ 2 = -3) : (C a : MvPolynomial (Fin 2) K) ^ 2 = -3 := by
  rw [← map_pow, ha]
  simp [map_ofNat]

/-- `f^*(U³-12aV²) = H³`. -/
theorem mapPullback_cuspEquation (a : K) (ha : a ^ 2 = -3) :
    mapPullback a (cuspEquation a) = H (C a) (X 0) (X 1) ^ 3 := by
  rw [← cusp_pullback_identity (C a) (X 0) (X 1) (C_sq_eq a ha)]
  simp [cuspEquation, map_mul, map_ofNat]

/-- The parametrization `s ↦ (αs², βs³)`. -/
def scaledParam (α β : K) : MvPolynomial (Fin 2) K →ₐ[K] Polynomial K :=
  aeval ![Polynomial.C α * Polynomial.X ^ 2, Polynomial.C β * Polynomial.X ^ 3]

/-- The coordinate scaling `U ↦ αU, V ↦ βV`. -/
def scaling (α β : K) : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K :=
  aeval ![C α * X 0, C β * X 1]

theorem scaling_comp_scaling {α β : K} (hα : α ≠ 0) (hβ : β ≠ 0) :
    (scaling α⁻¹ β⁻¹).comp (scaling α β) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change scaling α⁻¹ β⁻¹ (scaling α β (X 0)) = X 0
    simp only [scaling, aeval_X, Matrix.cons_val_zero, map_mul, aeval_C, MvPolynomial.algebraMap_eq]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hα, map_one, one_mul]
  · change scaling α⁻¹ β⁻¹ (scaling α β (X 1)) = X 1
    simp only [scaling, aeval_X, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_mul, aeval_C,
      MvPolynomial.algebraMap_eq]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hβ, map_one, one_mul]

@[simp] theorem scaledParam_X_zero (α β : K) :
    scaledParam α β (X 0) = Polynomial.C α * Polynomial.X ^ 2 := by
  simp [scaledParam]

@[simp] theorem scaledParam_X_one (α β : K) :
    scaledParam α β (X 1) = Polynomial.C β * Polynomial.X ^ 3 := by
  simp [scaledParam]

theorem scaledParam_eq (α β : K) :
    scaledParam α β = (CharZeroPaperCuspGeometry.planeParamPullback K).comp (scaling α β) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [scaledParam, scaling, CharZeroPaperCuspGeometry.planeParamPullback,
    Polynomial.algebraMap_eq]

theorem scaledParam_cuspEquation (a α β : K) (hrel : α ^ 3 = 12 * a * β ^ 2) :
    scaledParam α β (cuspEquation a) = 0 := by
  simp only [cuspEquation, scaledParam, map_sub, map_pow, map_mul, aeval_X, aeval_C,
    Polynomial.algebraMap_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have : (Polynomial.C (α ^ 3) : Polynomial K) = Polynomial.C (12 * a * β ^ 2) := by rw [hrel]
  simp only [map_pow, map_mul] at this
  linear_combination Polynomial.X ^ 6 * this

/-- Exact kernel: the parametrization cuts out precisely `U³ = 12aV²`. -/
theorem scaledParam_kernel [CharZero K] (a α β : K) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hrel : α ^ 3 = 12 * a * β ^ 2) :
    RingHom.ker (scaledParam α β).toRingHom = Ideal.span {cuspEquation a} := by
  ext p
  change scaledParam α β p = 0 ↔ p ∈ Ideal.span {cuspEquation a}
  rw [Ideal.mem_span_singleton]
  constructor
  · intro hp
    rw [scaledParam_eq] at hp
    have hk : scaling α β p ∈ Cusp.cuspIdeal K := by
      rw [← CharZeroPaperCuspBranch.planeParamPullback_kernel K]
      exact hp
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hk
    have hinv := congrArg (fun q => scaling α⁻¹ β⁻¹ q) hr
    have hpp : scaling α⁻¹ β⁻¹ (scaling α β p) = p := by
      have := congrArg (fun φ : MvPolynomial (Fin 2) K →ₐ[K] _ => φ p)
        (scaling_comp_scaling hα hβ)
      simpa using this
    rw [hpp] at hinv
    have e1 : (β⁻¹) ^ 2 = -(α ^ 3)⁻¹ * -(12 * a) := by
      field_simp
      linear_combination hrel
    have e2 : (α⁻¹) ^ 3 = (α ^ 3)⁻¹ := by rw [inv_pow]
    have hkey : scaling α⁻¹ β⁻¹ (X 1 ^ 2 - X 0 ^ 3) = C (-(α ^ 3)⁻¹) * cuspEquation a := by
      simp only [scaling, map_sub, map_pow, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, cuspEquation]
      rw [mul_pow, mul_pow, ← map_pow, ← map_pow, e1, e2]
      simp only [map_mul, map_neg]
      ring
    refine ⟨C (-(α ^ 3)⁻¹) * scaling α⁻¹ β⁻¹ r, ?_⟩
    rw [hinv, map_mul, hkey]
    ring
  · rintro ⟨r, rfl⟩
    rw [map_mul, scaledParam_cuspEquation a α β hrel, zero_mul]

/-- The ideal of `B`. -/
def bIdeal (a : K) : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {cuspEquation a}

theorem parameter_ne_zero' [CharZero K] (a : K) (ha : a ^ 2 = -3) : a ≠ 0 :=
  parameter_ne_zero a ha

/-- `α = β = 12a` is an admissible normalization scale. -/
theorem twelve_a_relation (a : K) : (12 * a) ^ 3 = 12 * a * (12 * a) ^ 2 := by ring

theorem bIdeal_isPrime [CharZero K] (a : K) (ha : a ^ 2 = -3) : (bIdeal a).IsPrime := by
  have h12 : (12 * a : K) ≠ 0 := mul_ne_zero (by norm_num) (parameter_ne_zero a ha)
  rw [bIdeal, ← scaledParam_kernel a (12 * a) (12 * a) h12 h12 (twelve_a_relation a)]
  exact RingHom.ker_isPrime _

/-- The coordinate ring of `B`. -/
abbrev BRing (a : K) := MvPolynomial (Fin 2) K ⧸ bIdeal a

/-- The cusp `B`, an actual affine scheme. -/
abbrev cuspB (a : K) : Scheme := Spec (.of (BRing a))

/-- `B ↪ 𝔸²`. -/
def cuspBImmersion (a : K) : cuspB a ⟶ plane K :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (bIdeal a)))

instance cuspBImmersion_isClosedImmersion (a : K) : IsClosedImmersion (cuspBImmersion a) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

theorem bRing_isDomain [CharZero K] (a : K) (ha : a ^ 2 = -3) : IsDomain (BRing a) := by
  have := bIdeal_isPrime a ha
  infer_instance

/-- `ex:branch-sing-B`: `B` is integral. -/
theorem cuspB_isIntegral [CharZero K] (a : K) (ha : a ^ 2 = -3) : IsIntegral (cuspB a) := by
  have := bRing_isDomain a ha
  infer_instance

/-- The parametrization descended to the coordinate ring of `B`. -/
def bParam (a α β : K) (hrel : α ^ 3 = 12 * a * β ^ 2) : BRing a →ₐ[K] Polynomial K :=
  Ideal.Quotient.liftₐ (bIdeal a) (scaledParam α β) (fun p hp => by
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hp
    rw [map_mul, scaledParam_cuspEquation a α β hrel, zero_mul])

@[simp] theorem bParam_mk (a α β : K) (hrel : α ^ 3 = 12 * a * β ^ 2) (p) :
    bParam a α β hrel (Ideal.Quotient.mk _ p) = scaledParam α β p := rfl

theorem bParam_injective [CharZero K] (a α β : K) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hrel : α ^ 3 = 12 * a * β ^ 2) : Function.Injective (bParam a α β hrel) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change p ∈ Ideal.span {cuspEquation a}
  rw [← scaledParam_kernel a α β hα hβ hrel]
  exact hq

/-- The image of the parametrization is the cusp subalgebra `k[s²,s³]`. -/
theorem scaledParam_range {α β : K} (hα : α ≠ 0) (hβ : β ≠ 0) :
    (scaledParam α β).range = Cusp.cuspAlg K := by
  rw [scaledParam, ← Algebra.adjoin_range_eq_range_aeval]
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · simpa [Polynomial.smul_eq_C_mul] using (Cusp.cuspAlg K).smul_mem (Cusp.X_sq_mem K) α
    · simpa [Polynomial.smul_eq_C_mul] using (Cusp.cuspAlg K).smul_mem (Cusp.X_cube_mem K) β
  · rw [Cusp.cuspAlg, Algebra.adjoin_le_iff]
    have h0 : Polynomial.C α * Polynomial.X ^ 2 ∈ Algebra.adjoin K (Set.range
        ![Polynomial.C α * (Polynomial.X : Polynomial K) ^ 2, Polynomial.C β * Polynomial.X ^ 3]) :=
      Algebra.subset_adjoin ⟨0, rfl⟩
    have h1 : Polynomial.C β * Polynomial.X ^ 3 ∈ Algebra.adjoin K (Set.range
        ![Polynomial.C α * (Polynomial.X : Polynomial K) ^ 2, Polynomial.C β * Polynomial.X ^ 3]) :=
      Algebra.subset_adjoin ⟨1, rfl⟩
    rintro _ (rfl | rfl)
    · have := Subalgebra.smul_mem _ h0 α⁻¹
      simpa [Polynomial.smul_eq_C_mul, ← mul_assoc, ← Polynomial.C_mul, hα] using this
    · have := Subalgebra.smul_mem _ h1 β⁻¹
      simpa [Polynomial.smul_eq_C_mul, ← mul_assoc, ← Polynomial.C_mul, hβ] using this

/-- `ex:branch-sing-B`: the coordinate ring of `B` is `k[s²,s³]`, compatibly with
`s ↦ (αs²,βs³)`. -/
def bRingEquivCusp [CharZero K] (a α β : K) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hrel : α ^ 3 = 12 * a * β ^ 2) : BRing a ≃ₐ[K] Cusp.cuspAlg K :=
  (AlgEquiv.ofInjective (bParam a α β hrel) (bParam_injective a α β hα hβ hrel)).trans
    (Subalgebra.equivOfEq _ _ (by
      rw [← scaledParam_range hα hβ]
      apply le_antisymm
      · rintro _ ⟨q, rfl⟩
        obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
        exact ⟨p, rfl⟩
      · rintro _ ⟨p, rfl⟩
        exact ⟨Ideal.Quotient.mk _ p, rfl⟩))

theorem bRingEquivCusp_apply [CharZero K] (a α β : K) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hrel : α ^ 3 = 12 * a * β ^ 2) (q : BRing a) :
    (bRingEquivCusp a α β hα hβ hrel q : Polynomial K) = bParam a α β hrel q := rfl

/-- The parameter is the birational coordinate `s = (α/β)·V/U`. -/
theorem parameter_birational (α β : K) (hβ : β ≠ 0) :
    Polynomial.X * scaledParam α β (X 0) = Polynomial.C (α / β) * scaledParam α β (X 1) := by
  simp only [scaledParam, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [show Polynomial.C (α / β) * (Polynomial.C β * Polynomial.X ^ 3) =
      Polynomial.C (α / β * β) * Polynomial.X ^ 3 by rw [Polynomial.C_mul]; ring,
    div_mul_cancel₀ _ hβ]
  ring

/-- The normalization parametrization `Spec k[s] → B`. -/
def normalizationParam (a α β : K) (hrel : α ^ 3 = 12 * a * β ^ 2) : line K ⟶ cuspB a :=
  Spec.map (CommRingCat.ofHom (bParam a α β hrel).toRingHom)

/-- The isomorphism `B ≅ Spec k[s²,s³]` induced by `bRingEquivCusp`. -/
def cuspBIso [CharZero K] (a α β : K) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hrel : α ^ 3 = 12 * a * β ^ 2) : CharZeroPaperCuspGeometry.cusp K ≅ cuspB a :=
  Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
    (bRingEquivCusp a α β hα hβ hrel).toRingEquiv).op

/-- The normalization parametrization of `B` is the existing cusp normalization
`Spec k[s] → Spec k[s²,s³]` transported along `B ≅ Spec k[s²,s³]`. -/
theorem normalizationParam_eq [CharZero K] (a α β : K) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hrel : α ^ 3 = 12 * a * β ^ 2) :
    normalizationParam a α β hrel =
      CharZeroPaperCuspGeometry.parametrization K ≫ (cuspBIso a α β hα hβ hrel).hom := by
  simp only [normalizationParam, CharZeroPaperCuspGeometry.parametrization, cuspBIso,
    Scheme.Spec_map, Functor.mapIso_hom, Iso.op_hom, RingEquiv.toCommRingCatIso_hom,
    ← Spec.map_comp]
  rfl

theorem normalizationParam_isFinite [CharZero K] (a α β : K) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hrel : α ^ 3 = 12 * a * β ^ 2) : IsFinite (normalizationParam a α β hrel) := by
  rw [normalizationParam_eq a α β hα hβ hrel]
  infer_instance

theorem normalizationParam_surjective [CharZero K] (a α β : K) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hrel : α ^ 3 = 12 * a * β ^ 2) : Surjective (normalizationParam a α β hrel) := by
  rw [normalizationParam_eq a α β hα hβ hrel]
  infer_instance

/-! ### The origin of `B` -/

theorem sub_C_constantCoeff_mem (I : Ideal (MvPolynomial (Fin 2) K)) (h0 : X 0 ∈ I)
    (h1 : X 1 ∈ I) (P : MvPolynomial (Fin 2) K) : P - C (constantCoeff P) ∈ I := by
  induction P using MvPolynomial.induction_on with
  | C b => simp
  | add p q hp hq =>
    rw [map_add, map_add, add_sub_add_comm]
    exact I.add_mem hp hq
  | mul_X p i hp =>
    have hi : X i ∈ I := by fin_cases i; exacts [h0, h1]
    simp only [map_mul, constantCoeff_X, mul_zero, map_zero, sub_zero]
    exact I.mul_mem_left p hi

/-- The maximal ideal of the origin of the target plane. -/
abbrev originIdeal (K : Type u) [Field K] : Ideal (MvPolynomial (Fin 2) K) :=
  RingHom.ker (constantCoeff : MvPolynomial (Fin 2) K →+* K)

instance originIdeal_isMaximal : (originIdeal K).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, by simp⟩)

theorem eq_originIdeal (I : Ideal (MvPolynomial (Fin 2) K)) [I.IsPrime] (h0 : X 0 ∈ I)
    (h1 : X 1 ∈ I) : I = originIdeal K := by
  refine ((originIdeal_isMaximal (K := K)).eq_of_le (Ideal.IsPrime.ne_top ‹_›) ?_).symm
  intro P hP
  have := sub_C_constantCoeff_mem I h0 h1 P
  rwa [show constantCoeff P = 0 from hP, map_zero, sub_zero] at this

theorem bIdeal_le_originIdeal (a : K) : bIdeal a ≤ originIdeal K := by
  rw [bIdeal, Ideal.span_le, Set.singleton_subset_iff]
  change constantCoeff (cuspEquation a) = 0
  simp [cuspEquation]

/-- The origin `(0,0)` of `B`, as an actual scheme point. -/
def originB (a : K) : PrimeSpectrum (BRing a) :=
  ⟨(originIdeal K).map (Ideal.Quotient.mk (bIdeal a)),
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact bIdeal_le_originIdeal a)⟩

theorem originB_comap (a : K) :
    (originB a).asIdeal.comap (Ideal.Quotient.mk (bIdeal a)) = originIdeal K := by
  change ((originIdeal K).map (Ideal.Quotient.mk (bIdeal a))).comap _ = _
  rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  exact sup_eq_left.mpr (bIdeal_le_originIdeal a)

/-- `originB` is the unique point of `B` at which both coordinates vanish. -/
theorem eq_originB_iff (a : K) (p : cuspB a) :
    p = originB a ↔ Ideal.Quotient.mk (bIdeal a) (X 0) ∈ p.asIdeal ∧
      Ideal.Quotient.mk (bIdeal a) (X 1) ∈ p.asIdeal := by
  constructor
  · rintro rfl
    constructor <;>
    · rw [← Ideal.mem_comap, originB_comap]
      simp
  · rintro ⟨h0, h1⟩
    have := p.isPrime.comap (Ideal.Quotient.mk (bIdeal a))
    have hq : p.asIdeal.comap (Ideal.Quotient.mk (bIdeal a)) = originIdeal K :=
      eq_originIdeal _ h0 h1
    apply PrimeSpectrum.ext
    apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    rw [hq, originB_comap]

/-! ### Critical lines and the restriction `g = f|_A` -/

/-- The source line `y = zx`, parametrized by `t ↦ (t,zt)`. -/
def linePullback (z : K) : MvPolynomial (Fin 2) K →ₐ[K] Polynomial K :=
  aeval ![Polynomial.X, Polynomial.C z * Polynomial.X]

theorem linePullback_surjective (z : K) : Function.Surjective (linePullback z) := by
  intro q
  refine ⟨Polynomial.aeval (X 0 : MvPolynomial (Fin 2) K) q, ?_⟩
  have : (linePullback z).comp (Polynomial.aeval (X 0 : MvPolynomial (Fin 2) K)) =
      AlgHom.id K _ := by
    apply Polynomial.algHom_ext
    simp [linePullback]
  exact congrArg (fun φ : Polynomial K →ₐ[K] Polynomial K => φ q) this

/-- The critical line `A_z ↪ 𝔸²`. -/
def sourceLine (z : K) : line K ⟶ plane K :=
  Spec.map (CommRingCat.ofHom (linePullback z).toRingHom)

instance sourceLine_isClosedImmersion (z : K) : IsClosedImmersion (sourceLine z) :=
  IsClosedImmersion.spec_of_surjective _ (linePullback_surjective z)

/-- On a critical line, `f` is squaring followed by `s ↦ (c₄s²,c₆s³)`. -/
theorem restriction_ring_square (a z : K) (hz : h a z = 0) :
    (linePullback z).comp (mapPullback a) =
      (Polynomial.expand K 2).comp (scaledParam (c4 a z) (c6 z)) := by
  have hz' : (Polynomial.C (z ^ 4 - 2 * a * z ^ 2 + 1) : Polynomial K) = 0 := by
    rw [show z ^ 4 - 2 * a * z ^ 2 + 1 = 0 from hz, map_zero]
  simp only [map_sub, map_add, map_mul, map_pow, map_one, map_ofNat] at hz'
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change linePullback z (mapPullback a (X 0)) =
      Polynomial.expand K 2 (scaledParam (c4 a z) (c6 z) (X 0))
    rw [mapPullback_X_zero]
    simp only [scaledParam, aeval_X, Matrix.cons_val_zero, F, linePullback, map_add, map_mul,
      map_pow, aeval_C, Polynomial.algebraMap_eq, map_ofNat, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Polynomial.expand_X, Polynomial.expand_C, c4]
    linear_combination Polynomial.X ^ 4 * hz'
  · change linePullback z (mapPullback a (X 1)) =
      Polynomial.expand K 2 (scaledParam (c4 a z) (c6 z) (X 1))
    rw [mapPullback_X_one]
    simp only [scaledParam, aeval_X, Matrix.cons_val_one, Matrix.cons_val_fin_one, G,
      linePullback, map_sub, map_mul, map_pow, Matrix.cons_val_zero, Polynomial.expand_X,
      Polynomial.expand_C, c6, map_one]
    ring

/-- The restriction `g : A_z → B`, defined as squaring followed by the
normalization parametrization with `(α,β) = (c₄,c₆)`. -/
def restriction [CharZero K] (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) : line K ⟶ cuspB a :=
  CharZeroPaperConeBranch.squareMap K ≫
    normalizationParam a (c4 a z) (c6 z) (line_coefficients_relation a z ha hz)

/-- `ex:branch-sing-B`: `g` is the restriction of `f` to `A_z`, landing in `B`. -/
theorem restriction_square [CharZero K] (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    restriction a z ha hz ≫ cuspBImmersion a = sourceLine z ≫ planeMap a := by
  simp only [restriction, normalizationParam, cuspBImmersion, sourceLine, planeMap,
    CharZeroPaperConeBranch.squareMap, CharZeroPaperConeBranch.squarePullback,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact congrArg AlgHom.toRingHom (restriction_ring_square a z hz).symm

instance cuspBImmersion_mono (a : K) : Mono (cuspBImmersion a) := inferInstance

/-- Uniqueness: any morphism `A_z → B` compatible with `f` is `g`. -/
theorem restriction_unique [CharZero K] (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0)
    (g : line K ⟶ cuspB a) (hg : g ≫ cuspBImmersion a = sourceLine z ≫ planeMap a) :
    g = restriction a z ha hz :=
  (cancel_mono (cuspBImmersion a)).mp (hg.trans (restriction_square a z ha hz).symm)

/-- The normalized lift of `g` is squaring. -/
theorem restriction_lift [CharZero K] (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    CharZeroPaperConeBranch.squareMap K ≫
      normalizationParam a (c4 a z) (c6 z) (line_coefficients_relation a z ha hz) =
      restriction a z ha hz := rfl

/-- The normalization parametrization sends the origin of `Spec k[s]` to the origin of `B`. -/
theorem normalizationParam_origin (a α β : K) (hrel : α ^ 3 = 12 * a * β ^ 2) :
    normalizationParam a α β hrel (CharZeroPaperConeBranch.axisDivisorPoint K).1 = originB a := by
  rw [eq_originB_iff]
  change bParam a α β hrel _ ∈ CharZeroPaperConeBranch.axisIdeal K ∧
    bParam a α β hrel _ ∈ CharZeroPaperConeBranch.axisIdeal K
  simp only [bParam_mk, scaledParam, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, CharZeroPaperConeBranch.axisIdeal]
  constructor
  · exact Ideal.mem_span_singleton.mpr ⟨Polynomial.C α * Polynomial.X, by ring⟩
  · exact Ideal.mem_span_singleton.mpr ⟨Polynomial.C β * Polynomial.X ^ 2, by ring⟩

/-- `ex:branch-sing-B`: the normalized lift `t ↦ t²` has the single branch divisor
`t = 0`, and the branch support of `g`, pushed to `B` by the normalization
parametrization, is exactly the origin of `B`. -/
theorem restriction_branch_eq_origin [CharZero K] (a z : K) (ha : a ^ 2 = -3)
    (hz : h a z = 0) :
    schemeReducedFiberBranch (CharZeroPaperConeBranch.squareMap K) =
        {CharZeroPaperConeBranch.axisDivisorPoint K} ∧
      normalizationParam a (c4 a z) (c6 z) (line_coefficients_relation a z ha hz) ''
        normalizedMorphismBranchSupport (CharZeroPaperConeBranch.squareMap K) = {originB a} := by
  refine ⟨CharZeroPaperConeBranch.square_reducedFiberBranch K, ?_⟩
  rw [CharZeroPaperConeBranch.normalized_square_branch_singleton, Set.image_singleton,
    normalizationParam_origin]
  rfl

/-! ### The four critical lines and their ramification index -/

/-- The source ring `k[x,y]`, regarded as a `k[U,V]`-algebra through `f`. A separate
type prevents confusion with the ring's action on itself. -/
@[nolint unusedArguments]
def SourceRing (_a : K) := MvPolynomial (Fin 2) K

instance (a : K) : CommRing (SourceRing a) := inferInstanceAs (CommRing (MvPolynomial (Fin 2) K))
instance (a : K) : IsDomain (SourceRing a) := inferInstanceAs (IsDomain (MvPolynomial (Fin 2) K))
instance (a : K) : IsNoetherianRing (SourceRing a) :=
  inferInstanceAs (IsNoetherianRing (MvPolynomial (Fin 2) K))
instance (a : K) : IsIntegrallyClosed (SourceRing a) :=
  inferInstanceAs (IsIntegrallyClosed (MvPolynomial (Fin 2) K))
instance (a : K) : Algebra K (SourceRing a) := inferInstanceAs (Algebra K (MvPolynomial (Fin 2) K))
instance sourceAlgebra (a : K) : Algebra (MvPolynomial (Fin 2) K) (SourceRing a) :=
  (mapPullback a).toRingHom.toAlgebra
instance (a : K) : IsScalarTower K (MvPolynomial (Fin 2) K) (SourceRing a) :=
  IsScalarTower.of_algebraMap_eq' (mapPullback a).comp_algebraMap.symm

/-- The identity of `k[x,y]`, viewed as a map into `SourceRing a`. -/
def toSource (a : K) : MvPolynomial (Fin 2) K →+* SourceRing a := RingHom.id _

theorem algebraMap_sourceRing (a : K) (p : MvPolynomial (Fin 2) K) :
    algebraMap (MvPolynomial (Fin 2) K) (SourceRing a) p = toSource a (mapPullback a p) := rfl

theorem sourceRing_finite [CharZero K] (a : K) (ha : a ^ 2 = -3) :
    Module.Finite (MvPolynomial (Fin 2) K) (SourceRing a) :=
  mapPullback_finite a ha

theorem sourceRing_faithful [CharZero K] (a : K) (ha : a ^ 2 = -3) :
    FaithfulSMul (MvPolynomial (Fin 2) K) (SourceRing a) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (mapPullback_injective a ha)

theorem planeMap_eq_algebraMap (a : K) :
    planeMap a =
      Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin 2) K) (SourceRing a))) :=
  rfl

/-- The linear form `y - zx`. -/
def lineForm (z : K) : MvPolynomial (Fin 2) K := X 1 - C z * X 0

/-- The shear `x ↦ x, y ↦ y - zx`. -/
def shear (z : K) : MvPolynomial (Fin 2) K ≃ₐ[K] MvPolynomial (Fin 2) K :=
  AlgEquiv.ofAlgHom (aeval ![X 0, X 1 - C z * X 0]) (aeval ![X 0, X 1 + C z * X 0])
    (by apply MvPolynomial.algHom_ext; intro i; fin_cases i <;> simp)
    (by apply MvPolynomial.algHom_ext; intro i; fin_cases i <;> simp)

theorem lineForm_prime (z : K) : Prime (lineForm z) := by
  have h : shear z (X 1) = lineForm z := by simp [shear, lineForm]
  rw [← h, MulEquiv.prime_iff]
  exact MvPolynomial.X_prime

/-- The source line `A_z = V(y-zx)`, as a height-one prime of `k[x,y]`. -/
def lineIdeal (a z : K) : Ideal (SourceRing a) := Ideal.span {toSource a (lineForm z)}

instance lineIdeal_isPrime (a z : K) : (lineIdeal a z).IsPrime :=
  (Ideal.span_singleton_prime (lineForm_prime z).ne_zero).mpr (lineForm_prime z)

theorem lineIdeal_height (a z : K) : (lineIdeal a z).height = 1 :=
  Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr (lineForm_prime z).ne_zero)
    (lineForm_prime z).not_isUnit

/-- The cofactor of `y - zx` in `H`. -/
def lineCofactor (a z : K) : MvPolynomial (Fin 2) K :=
  X 1 ^ 3 + C z * X 0 * X 1 ^ 2 + C (z ^ 2 - 2 * a) * X 0 ^ 2 * X 1 +
    C (z ^ 3 - 2 * a * z) * X 0 ^ 3

theorem H_eq_lineForm_mul (a z : K) (hz : h a z = 0) :
    H (C a) (X 0) (X 1) = lineForm z * lineCofactor a z := by
  have hz' : (C (z ^ 4 - 2 * a * z ^ 2 + 1) : MvPolynomial (Fin 2) K) = 0 := by
    rw [show z ^ 4 - 2 * a * z ^ 2 + 1 = 0 from hz, map_zero]
  simp only [map_sub, map_add, map_mul, map_pow, map_one, map_ofNat] at hz'
  simp only [H, lineForm, lineCofactor, map_sub, map_mul, map_pow, map_ofNat]
  linear_combination X 0 ^ 4 * hz'

/-- `y - zx` divides `H` exactly once. -/
theorem lineForm_not_dvd_cofactor [CharZero K] (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    ¬ lineForm z ∣ lineCofactor a z := by
  rintro ⟨q, hq⟩
  have he := congrArg (MvPolynomial.eval ![1, z]) hq
  simp only [lineForm, lineCofactor, map_add, map_mul, map_sub, map_pow, eval_X, eval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at he
  apply quartic_no_common_root a z ha hz
  linear_combination he

theorem lineForm_mem_lineIdeal (a z : K) : toSource a (lineForm z) ∈ lineIdeal a z :=
  Ideal.subset_span rfl

theorem cofactor_not_mem_lineIdeal [CharZero K] (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    toSource a (lineCofactor a z) ∉ lineIdeal a z := by
  intro hm
  exact lineForm_not_dvd_cofactor a z ha hz (Ideal.mem_span_singleton.mp hm)

theorem cuspEquation_ne_zero (a : K) : cuspEquation a ≠ 0 := by
  intro h0
  have := congrArg (MvPolynomial.eval ![1, 0]) h0
  simp [cuspEquation] at this

theorem cuspEquation_not_isUnit (a : K) : ¬ IsUnit (cuspEquation a) := by
  intro hu
  have := hu.map (constantCoeff : MvPolynomial (Fin 2) K →+* K)
  simp [cuspEquation] at this

theorem bIdeal_height (a : K) : (bIdeal a).height = 1 :=
  Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr (cuspEquation_ne_zero a)) (cuspEquation_not_isUnit a)

/-- `f(A_z) = B`: the line contracts to the cusp ideal. -/
theorem lineIdeal_under [CharZero K] (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    (lineIdeal a z).under (MvPolynomial (Fin 2) K) = bIdeal a := by
  have := sourceRing_finite a ha
  have := sourceRing_faithful a ha
  have := bIdeal_isPrime a ha
  have hle : bIdeal a ≤ (lineIdeal a z).under (MvPolynomial (Fin 2) K) := by
    rw [bIdeal, Ideal.span_le, Set.singleton_subset_iff]
    change toSource a (mapPullback a (cuspEquation a)) ∈ lineIdeal a z
    rw [mapPullback_cuspEquation a ha, H_eq_lineForm_mul a z hz, mul_pow, mul_comm, pow_succ,
      map_mul, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (lineForm_mem_lineIdeal a z))
  have : (bIdeal a).FiniteHeight := by
    simp [Ideal.finiteHeight_iff, bIdeal_height]
  refine (Ideal.eq_of_le_of_height_le (bIdeal a) hle ?_).symm
  rw [height_under_eq_of_finite_of_normal, lineIdeal_height, bIdeal_height]

/-- A quotient-length calculation in a localized DVR. -/
theorem ramificationIdx_eq_of_localIdealPower
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    (q : Ideal S) [q.IsPrime] (n : ℕ)
    [IsDiscreteValuationRing (Localization.AtPrime q)]
    (hmap : (q.under R).map (algebraMap R (Localization.AtPrime q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ n) :
    q.ramificationIdx R = n := by
  rw [Ideal.ramificationIdx_def, hmap, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal,
    ENat.toNat_natCast]

/-- `ex:branch-sing-B`: each critical line has ramification index three over `B`. -/
theorem lineIdeal_ramificationIdx [CharZero K] (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    (lineIdeal a z).ramificationIdx (MvPolynomial (Fin 2) K) = 3 := by
  let q := lineIdeal a z
  let Sq := Localization.AtPrime q
  have : IsDiscreteValuationRing Sq :=
    Pcf.isDiscreteValuationRing_localizationAtPrime_of_heightOne q (lineIdeal_height a z)
  apply ramificationIdx_eq_of_localIdealPower
  rw [lineIdeal_under a z ha hz, bIdeal, Ideal.map_span, Set.image_singleton,
    IsScalarTower.algebraMap_apply (MvPolynomial (Fin 2) K) (SourceRing a) Sq]
  change Ideal.span {(algebraMap (SourceRing a) Sq) (toSource a (mapPullback a (cuspEquation a)))}
    = _
  rw [mapPullback_cuspEquation a ha, H_eq_lineForm_mul a z hz, mul_pow, map_mul, map_pow,
    map_pow]
  have hunit : IsUnit (algebraMap (SourceRing a) Sq (toSource a (lineCofactor a z) ^ 3)) :=
    IsLocalization.map_units (M := q.primeCompl) Sq ⟨_, fun hm =>
      cofactor_not_mem_lineIdeal a z ha hz ((lineIdeal_isPrime a z).mem_of_pow_mem 3 hm)⟩
  rw [map_mul, Ideal.span_singleton_mul_right_unit hunit, map_pow, ← Ideal.span_singleton_pow]
  congr 1
  rw [← Set.image_singleton, ← Ideal.map_span]
  exact Localization.AtPrime.map_eq_maximalIdeal

/-! ### Unramifiedness away from `H = 0` -/

/-- Surjectivity of the cotangent map gives formal unramifiedness (first fundamental
exact sequence). -/
theorem formallyUnramified_of_cotangent_surjective
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (h : Function.Surjective (KaehlerDifferential.mapBaseChange R A B)) :
    Algebra.FormallyUnramified A B := by
  constructor
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨y, rfl⟩ := KaehlerDifferential.map_surjective R A B x
  obtain ⟨z, rfl⟩ := h y
  exact (KaehlerDifferential.exact_mapBaseChange_map R A B _).mpr ⟨z, rfl⟩

/-- A linear map between free modules of the same finite rank with invertible matrix
is surjective. -/
theorem linearMap_surjective_of_matrix_isUnit
    {R M N ι : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Fintype ι] [DecidableEq ι]
    (bM : Module.Basis ι R M) (bN : Module.Basis ι R N) (f : M →ₗ[R] N)
    (h : IsUnit (LinearMap.toMatrix bM bN f)) : Function.Surjective f := by
  rw [← Matrix.mulVec_surjective_iff_isUnit] at h
  intro y
  obtain ⟨x, hx⟩ := h (bN.equivFun y)
  refine ⟨bM.equivFun.symm x, bN.equivFun.injective ?_⟩
  have h' := f.toMatrix_mulVec_repr bM bN (bM.equivFun.symm x)
  change (LinearMap.toMatrix bM bN f).mulVec (bM.equivFun (bM.equivFun.symm x)) =
    bN.equivFun (f (bM.equivFun.symm x)) at h'
  rw [bM.equivFun.apply_symm_apply, hx] at h'
  exact h'.symm

section Unramified

variable [CharZero K] (a : K) (Q : Ideal (SourceRing a)) [Q.IsPrime]

instance localTower : IsScalarTower K (MvPolynomial (Fin 2) K) (Localization.AtPrime Q) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin 2) K) (SourceRing a)
        (Localization.AtPrime Q),
      ← IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 2) K) (SourceRing a),
      ← IsScalarTower.algebraMap_apply K (SourceRing a) (Localization.AtPrime Q)]

/-- The coordinate differential basis of the source ring. -/
def sourceBasis : Module.Basis (Fin 2) (SourceRing a) Ω[SourceRing a⁄K] :=
  KaehlerDifferential.mvPolynomialBasis K (Fin 2)

omit [CharZero K] in
theorem sourceBasis_apply (j : Fin 2) :
    sourceBasis a j = KaehlerDifferential.D K (SourceRing a) (toSource a (X j)) :=
  KaehlerDifferential.mvPolynomialBasis_apply K (Fin 2) j

/-- The coordinate differential basis of the source local ring. -/
def localBasis : Module.Basis (Fin 2) (Localization.AtPrime Q) Ω[Localization.AtPrime Q⁄K] := by
  let := Algebra.FormallyEtale.of_isLocalization (Rₘ := Localization.AtPrime Q) Q.primeCompl
  exact ((sourceBasis a).baseChange _).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (SourceRing a) _)

omit [CharZero K] in
theorem localBasis_apply (j : Fin 2) :
    localBasis a Q j = KaehlerDifferential.D K (Localization.AtPrime Q)
      (algebraMap (SourceRing a) _ (toSource a (X j))) := by
  simp only [localBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, sourceBasis_apply,
    KaehlerDifferential.map_D]

omit [CharZero K] in
theorem local_differential (P : MvPolynomial (Fin 2) K) :
    KaehlerDifferential.D K (Localization.AtPrime Q)
        (algebraMap (SourceRing a) _ (toSource a P)) =
      ∑ j : Fin 2, algebraMap (SourceRing a) (Localization.AtPrime Q) (toSource a (pderiv j P)) •
        localBasis a Q j := by
  have h₀ : KaehlerDifferential.D K (MvPolynomial (Fin 2) K) P =
      ∑ j : Fin 2, pderiv j P • KaehlerDifferential.D K (MvPolynomial (Fin 2) K) (X j) := by
    simpa using ((KaehlerDifferential.mvPolynomialBasis K (Fin 2)).sum_repr
      (KaehlerDifferential.D K (MvPolynomial (Fin 2) K) P)).symm
  have h : KaehlerDifferential.D K (SourceRing a) (toSource a P) =
      ∑ j : Fin 2, toSource a (pderiv j P) •
        KaehlerDifferential.D K (SourceRing a) (toSource a (X j)) := h₀
  have h' := congrArg (KaehlerDifferential.map K K (SourceRing a) (Localization.AtPrime Q)) h
  simp only [map_sum, map_smul, KaehlerDifferential.map_D] at h'
  rw [h']
  apply Finset.sum_congr rfl
  intro j _
  rw [localBasis_apply, algebraMap_smul]

omit [CharZero K] in
/-- In the coordinate bases, the cotangent map of `f` at `Q` is the Jacobian matrix. -/
theorem localCotangent_toMatrix :
    LinearMap.toMatrix
        ((KaehlerDifferential.mvPolynomialBasis K (Fin 2)).baseChange (Localization.AtPrime Q))
        (localBasis a Q)
        (KaehlerDifferential.mapBaseChange K (MvPolynomial (Fin 2) K) (Localization.AtPrime Q)) =
      (((algebraMap (SourceRing a) (Localization.AtPrime Q)).comp (toSource a)).mapMatrix
        (Matrix.of fun i j => pderiv i (mapPullback a (X j)))) := by
  ext i j
  simp only [LinearMap.toMatrix_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply, KaehlerDifferential.mapBaseChange_tmul,
    one_smul, KaehlerDifferential.map_D, RingHom.mapMatrix_apply, Matrix.map_apply,
    RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin 2) K) (SourceRing a)
    (Localization.AtPrime Q), algebraMap_sourceRing, local_differential]
  simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply]
  simp

omit [CharZero K] in
theorem jacobian_det (a : K) (ha : a ^ 2 = -3) :
    (Matrix.of fun i j : Fin 2 => pderiv i (mapPullback a (X j))).det =
      4 * H (C a) (X 0) (X 1) ^ 2 := by
  rw [Matrix.det_fin_two, ← jacobian_derivative_identity a ha]
  simp only [Matrix.of_apply, mapPullback_X_zero, mapPullback_X_one]
  ring

/-- `ex:branch-sing-B`: the Jacobian `4H²` is invertible off `H = 0`, so `f` is
unramified at every prime not containing `H`. -/
theorem isUnramifiedAt_of_H_not_mem (ha : a ^ 2 = -3)
    (hQ : toSource a (H (C a) (X 0) (X 1)) ∉ Q) :
    Algebra.IsUnramifiedAt (MvPolynomial (Fin 2) K) Q := by
  change Algebra.FormallyUnramified (MvPolynomial (Fin 2) K) (Localization.AtPrime Q)
  apply formallyUnramified_of_cotangent_surjective K
  apply linearMap_surjective_of_matrix_isUnit
    ((KaehlerDifferential.mvPolynomialBasis K (Fin 2)).baseChange (Localization.AtPrime Q))
    (localBasis a Q)
  rw [localCotangent_toMatrix, Matrix.isUnit_iff_isUnit_det, ← RingHom.map_det,
    jacobian_det a ha]
  apply IsLocalization.map_units (M := Q.primeCompl) (Localization.AtPrime Q)
    ⟨toSource a (4 * H (C a) (X 0) (X 1) ^ 2), ?_⟩
  change toSource a (4 * H (C a) (X 0) (X 1) ^ 2) ∉ Q
  rw [map_mul, map_pow]
  intro hm
  rcases (Ideal.IsPrime.mem_or_mem ‹_› hm) with h4 | hH
  · apply Ideal.IsPrime.ne_top ‹Q.IsPrime›
    rw [Ideal.eq_top_iff_one]
    have h1 : toSource a (C (4⁻¹ : K) * 4) ∈ Q := by
      rw [map_mul]
      exact Q.mul_mem_left _ h4
    have he : (C (4⁻¹ : K) * 4 : MvPolynomial (Fin 2) K) = 1 := by
      rw [← map_ofNat C 4, ← map_mul]
      norm_num
    rwa [he, map_one] at h1
  · exact hQ ((Ideal.IsPrime.mem_of_pow_mem ‹_› 2) hH)

theorem ramificationIdx_eq_one_of_H_not_mem (ha : a ^ 2 = -3)
    (hQ : toSource a (H (C a) (X 0) (X 1)) ∉ Q) :
    Q.ramificationIdx (MvPolynomial (Fin 2) K) = 1 := by
  have := isUnramifiedAt_of_H_not_mem a Q ha hQ
  have := sourceRing_finite a ha
  exact Ideal.ramificationIdx_eq_one Q _

end Unramified

/-! ### `Branch(f) = B` and `Z = ∅` -/

section Branch

variable [CharZero K] [IsAlgClosed K]

omit [CharZero K] [IsAlgClosed K] in
theorem quartic_monic (a : K) : (quartic a).Monic := by
  unfold quartic
  monicity!

open scoped Classical in
/-- Over an algebraically closed field, `h` is the product of its four linear factors. -/
theorem quartic_eq_prod (a : K) (ha : a ^ 2 = -3) :
    quartic a = ∏ z ∈ (quartic a).roots.toFinset, (Polynomial.X - Polynomial.C z) := by
  classical
  have hnd := Polynomial.nodup_roots (quartic_separable a ha)
  conv_lhs => rw [← Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (quartic_monic a)
    (IsAlgClosed.card_roots_eq_natDegree)]
  rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, hnd.dedup]

omit [CharZero K] [IsAlgClosed K] in
theorem homogenize_quartic (a : K) :
    (quartic a).homogenize 4 = H (C a) (X 0) (X 1 : MvPolynomial (Fin 2) K) := by
  simp only [quartic, Polynomial.homogenize_add, Polynomial.homogenize_sub,
    Polynomial.homogenize_C_mul, Polynomial.homogenize_X_pow (le_refl 4),
    Polynomial.homogenize_X_pow (show 2 ≤ 4 by norm_num), Polynomial.homogenize_one, H]
  simp only [map_mul, map_ofNat]
  ring

open scoped Classical in
/-- `H` is the product of the four distinct linear forms `x - zy`, `h(z) = 0`. -/
theorem H_eq_prod (a : K) (ha : a ^ 2 = -3) :
    H (C a) (X 0) (X 1 : MvPolynomial (Fin 2) K) =
      ∏ z ∈ (quartic a).roots.toFinset, (X 0 - C z * X 1) := by
  classical
  rw [← homogenize_quartic]
  conv_lhs => rw [quartic_eq_prod a ha]
  have hcard : ∑ _z ∈ (quartic a).roots.toFinset, (1 : ℕ) = 4 := by
    rw [Finset.sum_const, smul_eq_mul, mul_one, quartic_four_distinct_roots a ha]
  conv_lhs => rw [← hcard]
  rw [Polynomial.homogenize_finsetProd (fun z _ => by
    rw [Polynomial.natDegree_X_sub_C])]
  apply Finset.prod_congr rfl
  intro z _
  rw [Polynomial.homogenize_sub, Polynomial.homogenize_X one_ne_zero, Polynomial.homogenize_C]
  simp

omit [CharZero K] [IsAlgClosed K] in
theorem quartic_root_inv (a z : K) (hz : h a z = 0) : h a z⁻¹ = 0 := by
  have hz0 := quartic_root_ne_zero a z hz
  dsimp [h] at hz ⊢
  field_simp
  linear_combination hz

/-- A height-one prime containing `H` is one of the four critical lines. -/
theorem eq_lineIdeal_of_H_mem (a : K) (ha : a ^ 2 = -3) (Q : Ideal (SourceRing a)) [Q.IsPrime]
    (hQ : Q.height = 1) (hH : toSource a (H (C a) (X 0) (X 1)) ∈ Q) :
    ∃ w, h a w = 0 ∧ Q = lineIdeal a w := by
  classical
  rw [H_eq_prod a ha, map_prod, Ideal.IsPrime.prod_mem_iff] at hH
  obtain ⟨z, hz, hzQ⟩ := hH
  have hz' : h a z = 0 := by
    rw [← quartic_eval]
    exact (Polynomial.mem_roots (quartic_monic a).ne_zero).mp (Multiset.mem_toFinset.mp hz)
  have hz0 := quartic_root_ne_zero a z hz'
  refine ⟨z⁻¹, quartic_root_inv a z hz', ?_⟩
  have hfac : (X 0 - C z * X 1 : MvPolynomial (Fin 2) K) = C (-z) * lineForm z⁻¹ := by
    simp only [lineForm, map_neg]
    have hzz : C z * C z⁻¹ = (1 : MvPolynomial (Fin 2) K) := by
      rw [← map_mul, mul_inv_cancel₀ hz0, map_one]
    linear_combination (-(X 0 : MvPolynomial (Fin 2) K)) * hzz
  rw [hfac, map_mul] at hzQ
  rcases Ideal.IsPrime.mem_or_mem ‹_› hzQ with hc | hl
  · exfalso
    apply Ideal.IsPrime.ne_top ‹Q.IsPrime›
    rw [Ideal.eq_top_iff_one]
    have h1 := Q.mul_mem_left (toSource a (C (-z)⁻¹)) hc
    rwa [← map_mul, ← map_mul, inv_mul_cancel₀ (neg_ne_zero.mpr hz0), map_one, map_one] at h1
  · exact Ideal.eq_span_singleton_of_height_eq_one hQ hl (lineForm_prime z⁻¹)

/-- `ex:branch-sing-B`: the only critical integral effective divisors of `f` are the four
lines; every other height-one prime of the source has ramification index one. -/
theorem ramificationIdx_eq_one_of_ne_lines (a : K) (ha : a ^ 2 = -3) (Q : Ideal (SourceRing a))
    [Q.IsPrime] (hQ : Q.height = 1) (hne : ∀ w, h a w = 0 → Q ≠ lineIdeal a w) :
    Q.ramificationIdx (MvPolynomial (Fin 2) K) = 1 := by
  apply ramificationIdx_eq_one_of_H_not_mem a Q ha
  intro hH
  obtain ⟨w, hw, rfl⟩ := eq_lineIdeal_of_H_mem a ha Q hQ hH
  exact hne w hw rfl

/-- The divisor `B` of the target plane. -/
def bDivisorPoint (a : K) (ha : a ^ 2 = -3) : SchemeDivisorPoint (plane K) :=
  ⟨⟨bIdeal a, bIdeal_isPrime a ha⟩,
    (idealHeight_eq_coheight (.of (MvPolynomial (Fin 2) K))
      ⟨bIdeal a, bIdeal_isPrime a ha⟩).symm.trans
      (bIdeal_height a)⟩

omit [CharZero K] in
theorem exists_quartic_root (a : K) : ∃ z, h a z = 0 := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (quartic a) (by
    rw [Polynomial.degree_eq_natDegree (quartic_monic a).ne_zero, quartic_natDegree]
    norm_num)
  exact ⟨z, by rw [← quartic_eval]; exact hz⟩

/-- `ex:branch-sing-B`: `Branch(f) = B`, with the paper's reduced-fiber definition. -/
theorem planeMap_reducedFiberBranch (a : K) (ha : a ^ 2 = -3) :
    schemeReducedFiberBranch (planeMap a) = {bDivisorPoint a ha} := by
  have := sourceRing_finite a ha
  have := sourceRing_faithful a ha
  ext E
  let p : HeightOnePrime (MvPolynomial (Fin 2) K) :=
    ⟨E.1, (idealHeight_eq_coheight (.of (MvPolynomial (Fin 2) K)) E.1).trans E.2⟩
  have hiff := affineSchemeDivisorFiber_isReduced_iff_forall_ramificationIdx_eq_one
    (R := MvPolynomial (Fin 2) K) (S := SourceRing a) p
  change ¬ IsReduced ((planeMap a).fiber E.1) ↔ E = bDivisorPoint a ha
  rw [planeMap_eq_algebraMap]
  change ¬ IsReduced ((Spec.map (CommRingCat.ofHom
    (algebraMap (MvPolynomial (Fin 2) K) (SourceRing a)))).fiber p.1) ↔ _
  rw [hiff]
  constructor
  · intro hnot
    push Not at hnot
    obtain ⟨⟨Q, hQp, hlo⟩, hQ⟩ := hnot
    have hunder : Q.under (MvPolynomial (Fin 2) K) = E.1.asIdeal := hlo.over.symm
    have hheight : Q.height = 1 := by
      rw [← height_under_eq_of_finite_of_normal (R := MvPolynomial (Fin 2) K) Q, hunder]
      exact p.2
    by_cases hH : toSource a (H (C a) (X 0) (X 1)) ∈ Q
    · obtain ⟨w, hw, rfl⟩ := eq_lineIdeal_of_H_mem a ha Q hheight hH
      apply Subtype.ext
      apply PrimeSpectrum.ext
      rw [← hunder, lineIdeal_under a w ha hw]
      rfl
    · exact absurd (ramificationIdx_eq_one_of_H_not_mem a Q ha hH) hQ
  · rintro rfl hall
    obtain ⟨z, hz⟩ := exists_quartic_root a
    have hlo : (lineIdeal a z).LiesOver p.1.asIdeal := ⟨(lineIdeal_under a z ha hz).symm⟩
    have h1 := hall ⟨lineIdeal a z, inferInstance, hlo⟩
    rw [lineIdeal_ramificationIdx a z ha hz] at h1
    norm_num at h1

/-- `ex:branch-sing-B`: `Z`, the union of branch divisors other than `B`, is empty. -/
theorem otherBranch_empty (a : K) (ha : a ^ 2 = -3) :
    divisorSupport (schemeReducedFiberBranch (planeMap a) \ {bDivisorPoint a ha}) = ∅ := by
  rw [planeMap_reducedFiberBranch a ha, sdiff_self]
  simp [divisorSupport]

end Branch

/-! ### `B` as the image of the critical lines; the singular origin -/

/-- The closed subscheme `B` is the closure of the divisor point `B`. -/
theorem cuspBImmersion_range [CharZero K] (a : K) (ha : a ^ 2 = -3) :
    Set.range (cuspBImmersion a) = closure {(bDivisorPoint a ha).1} := by
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (bIdeal a))) = _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  change _ = closure ({(⟨bIdeal a, bIdeal_isPrime a ha⟩ : PrimeSpectrum (MvPolynomial (Fin 2) K))} :
    Set (PrimeSpectrum (MvPolynomial (Fin 2) K)))
  rw [PrimeSpectrum.closure_singleton]

/-- `f(A_z) = B` on generic points. -/
theorem planeMap_linePoint [CharZero K] (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    planeMap a (⟨lineIdeal a z, inferInstance⟩ : PrimeSpectrum (SourceRing a)) =
      (bDivisorPoint a ha).1 :=
  PrimeSpectrum.ext (lineIdeal_under a z ha hz)

section Singular

variable [CharZero K]

omit [CharZero K] in
theorem scaledParam_coeff_zero (α β : K) (P : MvPolynomial (Fin 2) K) :
    (scaledParam α β P).coeff 0 = constantCoeff P := by
  induction P using MvPolynomial.induction_on with
  | C b => simp [scaledParam]
  | add p q hp hq => rw [map_add, Polynomial.coeff_add, hp, hq, map_add]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.mul_coeff_zero, map_mul, constantCoeff_X, mul_zero]
    fin_cases i <;> simp [scaledParam]

omit [CharZero K] in
theorem mem_originB_iff (a : K) (P : MvPolynomial (Fin 2) K) :
    Ideal.Quotient.mk (bIdeal a) P ∈ (originB a).asIdeal ↔ constantCoeff P = 0 := by
  rw [← Ideal.mem_comap, originB_comap]
  rfl

omit [CharZero K] in
theorem ringKrullDim_bRing_le (a : K) : ringKrullDim (BRing a) ≤ 1 := by
  have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (mem_nonZeroDivisors_iff_ne_zero.mpr (cuspEquation_ne_zero a))
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  change ringKrullDim (BRing a) + 1 ≤ 0 + ((2 : ℕ) : WithBot ℕ∞) at h
  generalize ringKrullDim (BRing a) = d at h ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe n =>
    rw [zero_add] at h
    have h' : n + 1 ≤ 2 := by
      have : ((n + 1 : ℕ∞) : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞) := by
        simpa using h
      exact WithBot.coe_le_coe.mp this
    have h'' : n ≤ 1 := by
      rw [← one_add_one_eq_two] at h'
      exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h'
    exact_mod_cast h''

/-- `ex:branch-sing-B`: the local ring of `B` at the origin is not regular. -/
theorem origin_not_isRegular (a : K) (ha : a ^ 2 = -3) :
    ¬ IsRegularLocalRing (Localization.AtPrime (originB a).asIdeal) := by
  have := bRing_isDomain a ha
  let x : PrimeSpectrum (BRing a) := originB a
  have : x.asIdeal.IsPrime := x.isPrime
  let m := x.asIdeal
  let O := Localization.AtPrime m
  intro hreg
  have h12 : (12 * a : K) ≠ 0 := mul_ne_zero (by norm_num) (parameter_ne_zero a ha)
  have hrel := twelve_a_relation a
  have hdim : ringKrullDim O ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height m O]
    exact (Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsPrime.ne_top inferInstance)).trans
      (ringKrullDim_bRing_le a)
  have hinj : Function.Injective (algebraMap (BRing a) O) :=
    IsLocalization.injective O m.primeCompl_le_nonZeroDivisors
  let u : O := algebraMap (BRing a) O (Ideal.Quotient.mk _ (X 0))
  let v : O := algebraMap (BRing a) O (Ideal.Quotient.mk _ (X 1))
  have hu0 : u ≠ 0 := by
    intro hu
    have h0 := congrArg (bParam a (12 * a) (12 * a) hrel) (hinj (hu.trans (map_zero _).symm))
    simp only [bParam_mk, map_zero, scaledParam, aeval_X, Matrix.cons_val_zero] at h0
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr h12) (pow_ne_zero 2 Polynomial.X_ne_zero) h0
  have hnf : ¬ IsField O := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq]
    intro hm
    apply hu0
    have hmem : u ∈ IsLocalRing.maximalIdeal O := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ ((mem_originB_iff a _).mpr (by simp))
    rwa [hm, Ideal.mem_bot] at hmem
  have hfin : Module.finrank (IsLocalRing.ResidueField O) (IsLocalRing.CotangentSpace O) = 1 := by
    have h1 := (IsRegularLocalRing.iff_finrank_cotangentSpace O).mp hreg
    have hle : ((Module.finrank (IsLocalRing.ResidueField O) (IsLocalRing.CotangentSpace O) : ℕ∞) :
        WithBot ℕ∞) ≤ 1 := by
      rw [show ((Module.finrank (IsLocalRing.ResidueField O) (IsLocalRing.CotangentSpace O) : ℕ∞) :
        WithBot ℕ∞) = ringKrullDim O from h1]
      exact hdim
    have hne : Module.finrank (IsLocalRing.ResidueField O) (IsLocalRing.CotangentSpace O) ≠ 0 :=
      fun h0 => hnf (IsLocalRing.finrank_cotangentSpace_eq_zero_iff.mp h0)
    have : Module.finrank (IsLocalRing.ResidueField O) (IsLocalRing.CotangentSpace O) ≤ 1 := by
      exact_mod_cast hle
    omega
  have key := (IsDiscreteValuationRing.TFAE O hnf).out 6 4
  have hic : IsIntegrallyClosed O := (key.mp hfin).1
  -- The element `t = V/U` of the fraction field is integral but not in `O`.
  let L := FractionRing O
  let c : O := algebraMap K O (12 * a)
  have hc : IsUnit c := (IsUnit.mk0 _ h12).map (algebraMap K O)
  have hcusp : u ^ 3 = c * v ^ 2 := by
    have h0 : Ideal.Quotient.mk (bIdeal a) (cuspEquation a) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    rw [cuspEquation, map_sub, map_mul, map_pow, map_pow] at h0
    have h1 := congrArg (algebraMap (BRing a) O) h0
    rw [map_sub, map_mul, map_pow, map_pow, map_zero] at h1
    have hC : algebraMap (BRing a) O (Ideal.Quotient.mk (bIdeal a) (C (12 * a))) = c := by
      change _ = algebraMap K O (12 * a)
      rw [IsScalarTower.algebraMap_apply K (BRing a) O]
      rfl
    rw [hC] at h1
    exact sub_eq_zero.mp h1
  have huL : algebraMap O L u ≠ 0 := by
    rw [ne_eq, ← map_zero (algebraMap O L), (IsFractionRing.injective O L).eq_iff]
    exact hu0
  let t : L := algebraMap O L v / algebraMap O L u
  have hint : IsIntegral O t := by
    obtain ⟨cinv, hcinv⟩ := hc.exists_left_inv
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (cinv * u), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub_C _ (by norm_num)
    · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
      have hcL : algebraMap O L cinv * algebraMap O L c = 1 := by
        rw [← map_mul, hcinv, map_one]
      have hcuspL := congrArg (algebraMap O L) hcusp
      simp only [map_mul, map_pow] at hcuspL
      rw [sub_eq_zero]
      dsimp only [t]
      rw [div_pow, div_eq_iff (pow_ne_zero 2 huL), map_mul]
      linear_combination (-(algebraMap O L cinv)) * hcuspL - algebraMap O L v ^ 2 * hcL
  obtain ⟨o, ho⟩ := (isIntegrallyClosed_iff L).mp hic hint
  have huo : u * o = v := by
    apply IsFractionRing.injective O L
    rw [map_mul, ho]
    dsimp only [t]
    rw [mul_comm]
    exact div_mul_cancel₀ _ huL
  obtain ⟨⟨p, ⟨q, hq⟩⟩, rfl⟩ := IsLocalization.mk'_surjective m.primeCompl o
  have hpq : Ideal.Quotient.mk (bIdeal a) (X 0) * p = Ideal.Quotient.mk (bIdeal a) (X 1) * q := by
    apply hinj
    rw [map_mul, map_mul, ← IsLocalization.mk'_spec O p ⟨q, hq⟩, ← mul_assoc]
    change u * _ * _ = v * _
    rw [huo]
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective p
  obtain ⟨R, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hR : constantCoeff R ≠ 0 := fun h0 => hq ((mem_originB_iff a R).mpr h0)
  have he := congrArg (bParam a (12 * a) (12 * a) hrel) hpq
  simp only [← map_mul, bParam_mk] at he
  simp only [map_mul, scaledParam_X_zero, scaledParam_X_one] at he
  have hP : scaledParam (12 * a) (12 * a) P = Polynomial.X * scaledParam (12 * a) (12 * a) R := by
    have hne : (Polynomial.C (12 * a) * Polynomial.X ^ 2 : Polynomial K) ≠ 0 :=
      mul_ne_zero (Polynomial.C_ne_zero.mpr h12) (pow_ne_zero 2 Polynomial.X_ne_zero)
    apply mul_left_cancel₀ hne
    rw [Polynomial.C_mul]
    linear_combination he
  have h1 := congrArg (fun p : Polynomial K => p.coeff 1) hP
  simp only [Polynomial.coeff_X_mul, scaledParam_coeff_zero] at h1
  apply hR
  rw [← h1]
  apply Cusp.coeff_one_eq_zero_of_mem
  rw [← scaledParam_range h12 h12]
  exact ⟨P, rfl⟩

/-- `ex:branch-sing-B`: the origin lies in `Sing(B)`. -/
theorem originB_mem_singularLocus (a : K) (ha : a ^ 2 = -3) :
    originB a ∈ stalkSingularLocus (cuspB a) := by
  intro hreg
  exact origin_not_isRegular a ha
    (IsRegularLocalRing.of_ringEquiv
      (Spec.stalkIso (.of (BRing a)) (originB a)).commRingCatIsoToRingEquiv)

omit [CharZero K] in
/-- The ambient target plane is smooth, so `Sing(Y) = ∅`. -/
theorem plane_singularLocus_empty : stalkSingularLocus (plane K) = ∅ := by
  let f : plane K ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin 2) K)))
  have : Smooth f :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  exact hp (isRegularLocalRing_stalk_of_mem_smoothLocus (.of K) f p
    (by rw [Scheme.Hom.smoothLocus_eq_top]; trivial))

end Singular

/-! ### The canonical normalization of `B` and the normalized branch of `g` -/

section Canonical

variable [CharZero K]

open CharZeroPaperCuspGeometry CharZeroPaperCuspCanonical

theorem restriction_isFinite (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    IsFinite (restriction a z ha hz) := by
  obtain ⟨hc4, hc6⟩ := line_coefficients_ne_zero a z ha hz
  have := normalizationParam_isFinite a (c4 a z) (c6 z) hc4 hc6
    (line_coefficients_relation a z ha hz)
  unfold restriction
  infer_instance

theorem restriction_surjective (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    Surjective (restriction a z ha hz) := by
  obtain ⟨hc4, hc6⟩ := line_coefficients_ne_zero a z ha hz
  have := normalizationParam_surjective a (c4 a z) (c6 z) hc4 hc6
    (line_coefficients_relation a z ha hz)
  unfold restriction
  infer_instance

/-- `Spec k[s]` is the canonical normalization of `B`, via `s ↦ (c₄s²,c₆s³)`. -/
def bNormalizationIso (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    line K ≅ (haveI := cuspB_isIntegral a ha; Palomar.normalization (cuspB a)) :=
  haveI := cuspB_isIntegral a ha
  let e := cuspBIso a (c4 a z) (c6 z) (line_coefficients_ne_zero a z ha hz).1
    (line_coefficients_ne_zero a z ha hz).2 (line_coefficients_relation a z ha hz)
  haveI := CharZeroPaperSmoothBranch.normalizationMorphism_isIso_of_isIso e.hom
  parameterLineNormalizationIso K ≪≫ asIso (schemeGlobalNormalizationMorphism e.hom)

/-- `ex:branch-sing-B`: under `bNormalizationIso`, the canonical normalization map of `B`
is the parametrization `s ↦ (c₄s²,c₆s³)`. -/
theorem bNormalizationIso_comm (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    haveI := cuspB_isIntegral a ha
    (bNormalizationIso a z ha hz).hom ≫ Palomar.normalizationMap (cuspB a) =
      normalizationParam a (c4 a z) (c6 z) (line_coefficients_relation a z ha hz) := by
  have := cuspB_isIntegral a ha
  simp only [bNormalizationIso, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [schemeGlobalNormalizationMorphism_comp, ← Category.assoc,
    parameterLineNormalizationIso_comm, normalizationParam_eq]

/-- `ex:branch-sing-B`: the canonical normalized lift of `g` is `t ↦ t²`. -/
theorem restriction_normalizedLift (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    haveI := cuspB_isIntegral a ha
    haveI := restriction_isFinite a z ha hz
    haveI := restriction_surjective a z ha hz
    schemeGlobalNormalizationMorphism (restriction a z ha hz) =
      Palomar.normalizationMap (line K) ≫
        CharZeroPaperConeBranch.squareMap K ≫ (bNormalizationIso a z ha hz).hom := by
  have := cuspB_isIntegral a ha
  have := restriction_isFinite a z ha hz
  have := restriction_surjective a z ha hz
  have := bRing_isDomain a ha
  exact schemeGlobalNormalizationMorphism_eq_of_factor (.of (BRing a)) _ _
    (by rw [Category.assoc, bNormalizationIso_comm]; rfl)

/-- `ex:branch-sing-B`: `Branch(g) = {(0,0)}`, for the actual canonical normalized
branch support of `g`. -/
theorem restriction_normalizedBranch (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    haveI := cuspB_isIntegral a ha
    haveI := restriction_isFinite a z ha hz
    haveI := restriction_surjective a z ha hz
    normalizedMorphismBranchSupport (restriction a z ha hz) = {originB a} := by
  have := cuspB_isIntegral a ha
  have := restriction_isFinite a z ha hz
  have := restriction_surjective a z ha hz
  let ψ := bNormalizationIso a z ha hz
  have : IsLocallyNoetherian (Palomar.normalization (cuspB a)) :=
    isLocallyNoetherian_of_isOpenImmersion ψ.inv
  have : IsIso (Palomar.normalizationMap (line K)) := normalScheme_normalizationMap_isIso _
  have : IsLocallyNoetherian (Palomar.normalization (line K)) :=
    isLocallyNoetherian_of_isOpenImmersion (Palomar.normalizationMap (line K))
  have hsq : divisorSupport (schemeReducedFiberBranch (CharZeroPaperConeBranch.squareMap K)) =
      {(CharZeroPaperConeBranch.axisDivisorPoint K).1} := by
    rw [← CharZeroPaperSmoothBranch.normalized_support_eq_reduced_support,
      CharZeroPaperConeBranch.normalized_square_branch_singleton]
  have h₁ := reducedFiberBranch_support_tower
    (Palomar.normalizationMap (line K) ≫ CharZeroPaperConeBranch.squareMap K) ψ.hom
  have h₂ := reducedFiberBranch_support_tower
    (Palomar.normalizationMap (line K)) (CharZeroPaperConeBranch.squareMap K)
  rw [CharZeroPaperSmoothBranch.iso_reducedFiberBranch_empty ψ.hom] at h₁
  rw [CharZeroPaperSmoothBranch.iso_reducedFiberBranch_empty
    (Palomar.normalizationMap (line K))] at h₂
  simp only [divisorSupport, Set.mem_empty_iff_false, Set.iUnion_of_empty, Set.iUnion_empty,
    Set.image_empty, Set.union_empty, Set.empty_union] at h₁ h₂
  unfold normalizedMorphismBranchSupport
  rw [restriction_normalizedLift, ← Category.assoc]
  simp only [divisorSupport] at hsq ⊢
  rw [h₁, h₂, hsq, Set.image_singleton, Set.image_singleton, ← Scheme.Hom.comp_apply,
    bNormalizationIso_comm, normalizationParam_origin]
  rfl

end Canonical

/-! ### The conclusion: the `Sing(B)` term cannot be dropped -/

/-- `ex:branch-sing-B`, conclusion. For the restriction `g = f|_{A_z} : A_z → B` to a
critical line, the canonical normalized branch support of `g` is the origin of `B`;
`Z` (the branch support of `f` other than `B`) is empty; the target plane `Y` has empty
singular locus; and the origin lies in `Sing(B)`. Hence the branch point of `g` lies
outside `(B ∩ Z) ∪ (B ∩ Sing Y)` and is accounted for only by `Sing(B)`. -/
theorem sing_term_necessary [CharZero K] [IsAlgClosed K] (a z : K) (ha : a ^ 2 = -3)
    (hz : h a z = 0) :
    haveI := cuspB_isIntegral a ha
    haveI := restriction_isFinite a z ha hz
    haveI := restriction_surjective a z ha hz
    normalizedMorphismBranchSupport (restriction a z ha hz) = {originB a} ∧
      schemeReducedFiberBranch (planeMap a) = {bDivisorPoint a ha} ∧
      divisorSupport (schemeReducedFiberBranch (planeMap a) \ {bDivisorPoint a ha}) = ∅ ∧
      stalkSingularLocus (plane K) = ∅ ∧
      originB a ∈ stalkSingularLocus (cuspB a) :=
  ⟨restriction_normalizedBranch a z ha hz, planeMap_reducedFiberBranch a ha,
    otherBranch_empty a ha, plane_singularLocus_empty, originB_mem_singularLocus a ha⟩

end Pcf.Examples.CharZeroPaperSingularImageGeometry

#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.mapPullback_injective
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.mapPullback_finite
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.planeMap_isFinite
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.planeMap_surjective
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.mapPullback_cuspEquation
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.scaledParam_kernel
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.bIdeal_isPrime
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.cuspB_isIntegral
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.bRingEquivCusp
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.parameter_birational
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.normalizationParam_eq
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.normalizationParam_isFinite
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.normalizationParam_surjective
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.eq_originB_iff
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.restriction_ring_square
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.restriction_square
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.restriction_unique
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.restriction_lift
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.normalizationParam_origin
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.restriction_branch_eq_origin
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.lineForm_prime
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.lineIdeal_height
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.H_eq_lineForm_mul
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.lineForm_not_dvd_cofactor
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.lineIdeal_under
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.lineIdeal_ramificationIdx
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.localCotangent_toMatrix
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.jacobian_det
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.isUnramifiedAt_of_H_not_mem
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.ramificationIdx_eq_one_of_H_not_mem
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.quartic_eq_prod
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.H_eq_prod
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.eq_lineIdeal_of_H_mem
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.ramificationIdx_eq_one_of_ne_lines
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.planeMap_reducedFiberBranch
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.otherBranch_empty
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.cuspBImmersion_range
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.planeMap_linePoint
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.ringKrullDim_bRing_le
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.origin_not_isRegular
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.originB_mem_singularLocus
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.plane_singularLocus_empty
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.bNormalizationIso
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.bNormalizationIso_comm
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.restriction_normalizedLift
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.restriction_normalizedBranch
#print axioms Pcf.Examples.CharZeroPaperSingularImageGeometry.sing_term_necessary
