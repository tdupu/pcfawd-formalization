/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPPrimaryFibresConstruction
public import Pcf.Bounding.PrimaryFibres

/-!
# `B'` and `E'` in `lem:primary-fibres` are the paper's normalizations

`paper-p.tex`, proof of Lemma `lem:primary-fibres`: "Let `B'` be the normalization of `B` in
`K'`, and `E'` the normalization of `(E ×_B B')_red`. Purely inseparable base change is a
universal homeomorphism, so the latter reduction is integral."

On affine charts (`B = Spec A`, `E ⊇ Spec R`, `A' = baseNorm`, `R' = sourceNorm`):
* `baseNorm_isNormalization`: `A'` is the integral closure of `A` in `K'`, integrally closed
  with fraction field `K'` — `B'` is the normalization of `B` in `K'`.
* `sourceNorm_isNormalization_tensorReduced`: for `φ : R ⊗_A A' → R'`, `ker φ` is the nilradical
  (`ker_paperTensorMap`, via `p`-powers: `exists_pow_eq_tmul_one`), so
  `(R ⊗_A A')_red ≅ im φ` (`tensorReducedEquivRange`; in particular it is a domain);
  `R'` is exactly the set of elements of `L'` integral over `R ⊗_A A'`; every element of `L'`
  is a quotient of elements of `im φ`; and `R'` is integrally closed with fraction field `L'`.
  Hence `R'` is the normalization of `(R ⊗_A A')_red` — `E'` on the chart.
* `primaryFibres_affine_paperRoute`: the lemma's literal statement on the affine chart.
-/

@[expose] public section

namespace Pcf.Bounding.PaperPPrimaryFibres

set_option linter.style.haveILetI false

universe u

open IntermediateField
open scoped TensorProduct

noncomputable section

open scoped Pcf.Bounding.PaperPPrimaryFibres

variable (A R : Type u) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R]
  [FaithfulSMul A R] (T : Finset (PaperOmega R))

/-- The canonical map `R ⊗_A A' → R'`, `r ⊗ a ↦ r·a`. -/
def paperTensorMap : R ⊗[A] baseNorm A R T →ₐ[A] sourceNorm R T :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A R (sourceNorm R T))
    (IsScalarTower.toAlgHom A (baseNorm A R T) (sourceNorm R T)) (fun _ _ => .all _ _)

theorem paperTensorMap_tmul (r : R) (a : baseNorm A R T) :
    paperTensorMap A R T (r ⊗ₜ a) =
      algebraMap R (sourceNorm R T) r * algebraMap (baseNorm A R T) (sourceNorm R T) a :=
  Algebra.TensorProduct.lift_tmul _ _ _ r a

theorem coe_paperTensorMap_tmul (r : R) (a : baseNorm A R T) :
    (((paperTensorMap A R T (r ⊗ₜ a) : sourceNorm R T) : sourceAlt R T) : PaperOmega R) =
      algebraMap R (PaperOmega R) r * ((a : baseAlt A R T) : PaperOmega R) := by
  rw [paperTensorMap_tmul]
  change ((algebraMap R (sourceNorm R T) r : sourceNorm R T) : sourceAlt R T).1 *
    (((algebraMap (baseNorm A R T) (sourceNorm R T) a : sourceNorm R T) : sourceAlt R T) :
      PaperOmega R) = _
  rw [coe_algebraMap_norm]; rfl

theorem paperTensorMap_tmul_one (r : R) :
    paperTensorMap A R T (r ⊗ₜ 1) = algebraMap R (sourceNorm R T) r := by
  rw [paperTensorMap_tmul, map_one, mul_one]

variable [IsIntegrallyClosed A]
  (hT : (T : Set (PaperOmega R)) ⊆ perfectClosure (FractionRing A) (PaperOmega R))
  (p : ℕ) [hp : Fact p.Prime] [CharP A p]

include hT in
/-- Every element of `R ⊗_A A'` has a `p`-power in `R ⊗ 1` (`A'` is radicial over `A`). -/
theorem exists_pow_eq_tmul_one (x : R ⊗[A] baseNorm A R T) [CharP (R ⊗[A] baseNorm A R T) p] :
    ∃ (n : ℕ) (y : R), x ^ (p ^ n) = y ⊗ₜ 1 := by
  haveI := baseAlt_isPurelyInseparable A R T hT
  haveI : CharP (FractionRing A) p :=
    charP_of_injective_algebraMap (IsFractionRing.injective A (FractionRing A)) p
  haveI : ExpChar (FractionRing A) p := (expChar_prime_iff _ hp.out).mpr inferInstance
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    obtain ⟨n, b, hb⟩ := PrimaryFibres.integralClosure_pow_mem_base (R := A)
      (K := FractionRing A) (L := baseAlt A R T) p a
    have hb' : a ^ (p ^ n) = algebraMap A (baseNorm A R T) b := Subtype.ext (by
      simpa using hb)
    refine ⟨n, b • r ^ (p ^ n), ?_⟩
    rw [Algebra.TensorProduct.tmul_pow, hb', Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add x x' hx hx' =>
    obtain ⟨n, y, hy⟩ := hx
    obtain ⟨m, y', hy'⟩ := hx'
    refine ⟨n + m, y ^ (p ^ m) + y' ^ (p ^ n), ?_⟩
    rw [add_pow_char_pow, pow_add, pow_mul, hy, mul_comm, pow_mul, hy',
      Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow, one_pow, one_pow,
      TensorProduct.add_tmul]

include hT p in
/-- **`(R ⊗_A A')_red ↪ R'`.** The kernel of `R ⊗_A A' → R'` is the nilradical. -/
theorem ker_paperTensorMap :
    RingHom.ker (paperTensorMap A R T) = nilradical (R ⊗[A] baseNorm A R T) := by
  set φ := paperTensorMap A R T
  apply le_antisymm
  · intro x hx
    haveI : Nontrivial (R ⊗[A] baseNorm A R T) := φ.toRingHom.domain_nontrivial
    have hinj : Function.Injective (algebraMap A (R ⊗[A] baseNorm A R T)) := by
      intro a b h
      apply algebraMap_A_baseNorm_injective A R T
      apply algebraMap_norm_injective A R T
      have := congrArg φ h
      rwa [AlgHom.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply A (baseNorm A R T),
        IsScalarTower.algebraMap_apply A (baseNorm A R T) (sourceNorm R T) b] at this
    haveI : CharP (R ⊗[A] baseNorm A R T) p := charP_of_injective_algebraMap hinj p
    obtain ⟨n, y, hy⟩ := exists_pow_eq_tmul_one A R T hT p x
    have h0 : φ (x ^ (p ^ n)) = 0 := by rw [map_pow, (RingHom.mem_ker).mp hx, zero_pow
      (pow_ne_zero _ hp.out.ne_zero)]
    rw [hy, paperTensorMap_tmul_one] at h0
    have hy0 : y = 0 := algebraMap_R_sourceNorm_injective R T (by rw [h0, map_zero])
    exact ⟨p ^ n, by rw [hy, hy0, TensorProduct.zero_tmul]; exact Ideal.zero_mem _⟩
  · intro x hx
    obtain ⟨n, hn⟩ := hx
    rw [RingHom.mem_ker]
    exact IsReduced.eq_zero _ ⟨n, by rw [← map_pow, hn, map_zero]⟩

include hT p in
/-- The induced injection `(R ⊗_A A')_red ≃ image ⊆ R'`. -/
def tensorReducedEquivRange :
    (R ⊗[A] baseNorm A R T) ⧸ nilradical (R ⊗[A] baseNorm A R T) ≃+*
      (paperTensorMap A R T).toRingHom.range :=
  (Ideal.quotEquivOfEq (by
    rw [← ker_paperTensorMap A R T hT p]; rfl)).trans
    (RingHom.quotientKerEquivRange (paperTensorMap A R T).toRingHom)

/-- `R ⊗_A A' → R' ⊆ L' ⊆ Ω`. -/
def paperTensorToOmega : R ⊗[A] baseNorm A R T →+* PaperOmega R :=
  (algebraMap (sourceAlt R T) (PaperOmega R)).comp
    ((algebraMap (sourceNorm R T) (sourceAlt R T)).comp (paperTensorMap A R T).toRingHom)

omit [IsIntegrallyClosed A] in
theorem paperTensorToOmega_tmul (r : R) (a : baseNorm A R T) :
    paperTensorToOmega A R T (r ⊗ₜ a) =
      algebraMap R (PaperOmega R) r * ((a : baseAlt A R T) : PaperOmega R) :=
  coe_paperTensorMap_tmul A R T r a

omit [IsIntegrallyClosed A] in
include hT in
/-- **`R'`, the image of `R ⊗_A A'`, and `L'` share the fraction field.** Every element of
`L'` is a quotient of two elements of the image of `R ⊗_A A'`. -/
theorem sourceAlt_mem_fractions_paperTensor (x : PaperOmega R) (hx : x ∈ sourceAlt R T) :
    ∃ y ∈ (paperTensorToOmega A R T).range, ∃ z ∈ (paperTensorToOmega A R T).range,
      y / z = x := by
  set ψ := paperTensorToOmega A R T
  have hR : ∀ r : R, algebraMap R (PaperOmega R) r ∈ ψ.range := fun r =>
    ⟨r ⊗ₜ 1, by rw [paperTensorToOmega_tmul]; simp⟩
  have hA : ∀ a : baseNorm A R T, ((a : baseAlt A R T) : PaperOmega R) ∈ ψ.range := fun a =>
    ⟨1 ⊗ₜ a, by rw [paperTensorToOmega_tmul, map_one, one_mul]⟩
  have key : (sourceAlt R T).toSubfield ≤ Subfield.closure (ψ.range : Set (PaperOmega R)) := by
    rw [adjoin_toSubfield]
    refine Subfield.closure_le.mpr (Set.union_subset ?_ ?_)
    · rintro _ ⟨z, rfl⟩
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R) z
      rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
      exact Subfield.div_mem _ (Subfield.subset_closure (hR a))
        (Subfield.subset_closure (hR b))
    · intro t ht
      haveI := baseAlt_finiteDimensional A R T hT
      haveI : IsFractionRing (baseNorm A R T) (baseAlt A R T) :=
        integralClosure.isFractionRing_of_finite_extension (FractionRing A) _
      obtain ⟨a, b, -, he⟩ := IsFractionRing.div_surjective (A := baseNorm A R T)
        (⟨t, subset_adjoin _ _ ht⟩ : baseAlt A R T)
      have he' := congrArg (fun w : baseAlt A R T => (w : PaperOmega R)) he
      simp only [IntermediateField.coe_div] at he'
      rw [← he']
      exact Subfield.div_mem _ (Subfield.subset_closure (hA a)) (Subfield.subset_closure (hA b))
  obtain ⟨y, hy, z, hz, hyz⟩ := Subfield.mem_closure_iff.mp (key hx)
  rw [Subring.closure_eq] at hy hz
  exact ⟨y, hy, z, hz, hyz⟩

omit [IsIntegrallyClosed A] in
include hT in
/-- **`B'` is the normalization of `B` in `K'`** (affine chart): `A' = baseNorm` is the integral
closure of `A` in `K'`, it is integrally closed with fraction field `K'`, and finite over `A`. -/
theorem baseNorm_isNormalization :
    (∀ x : baseAlt A R T, x ∈ baseNorm A R T ↔ IsIntegral A x) ∧
      IsIntegrallyClosed (baseNorm A R T) ∧ IsFractionRing (baseNorm A R T) (baseAlt A R T) := by
  haveI := baseAlt_finiteDimensional A R T hT
  exact ⟨fun x => mem_integralClosure_iff A _, baseNorm_isIntegrallyClosed A R T hT,
    integralClosure.isFractionRing_of_finite_extension (FractionRing A) _⟩

include hT p in
/-- **`E'` is the normalization of `(E ×_B B')_red`** (affine chart). With
`φ : R ⊗_A A' → R'`: `ker φ` is the nilradical (so `(R ⊗_A A')_red` is the image of `φ`);
an element of `L'` lies in `R'` iff it is integral over `R ⊗_A A'` (so `R'` is the integral
closure of the image in `L'`); every element of `L'` is a quotient of elements of the image
(common fraction field); and `R'` is integrally closed with fraction field `L'`. -/
theorem sourceNorm_isNormalization_tensorReduced :
    letI : Algebra (R ⊗[A] baseNorm A R T) (sourceAlt R T) :=
      ((algebraMap (sourceNorm R T) (sourceAlt R T)).comp
        (paperTensorMap A R T).toRingHom).toAlgebra
    RingHom.ker (paperTensorMap A R T) = nilradical (R ⊗[A] baseNorm A R T) ∧
      (∀ x : sourceAlt R T, x ∈ sourceNorm R T ↔ IsIntegral (R ⊗[A] baseNorm A R T) x) ∧
      (∀ x ∈ sourceAlt R T, ∃ y ∈ (paperTensorToOmega A R T).range,
        ∃ z ∈ (paperTensorToOmega A R T).range, y / z = x) ∧
      IsIntegrallyClosed (sourceNorm R T) ∧ IsFractionRing (sourceNorm R T) (sourceAlt R T) := by
  letI : Algebra (R ⊗[A] baseNorm A R T) (sourceAlt R T) :=
    ((algebraMap (sourceNorm R T) (sourceAlt R T)).comp
      (paperTensorMap A R T).toRingHom).toAlgebra
  letI : Algebra (R ⊗[A] baseNorm A R T) (sourceNorm R T) :=
    (paperTensorMap A R T).toRingHom.toAlgebra
  haveI : IsScalarTower (R ⊗[A] baseNorm A R T) (sourceNorm R T) (sourceAlt R T) :=
    .of_algebraMap_eq' rfl
  haveI := sourceAlt_finiteDimensional A R T hT
  refine ⟨ker_paperTensorMap A R T hT p, fun x => ⟨fun hx => ?_, fun hx => ?_⟩,
    sourceAlt_mem_fractions_paperTensor A R T hT, sourceNorm_isIntegrallyClosed A R T hT,
    integralClosure.isFractionRing_of_finite_extension (FractionRing R) _⟩
  · have hy : IsIntegral R (⟨x, hx⟩ : sourceNorm R T) := integralClosure.isIntegral _
    have h2 : IsIntegral (R ⊗[A] baseNorm A R T)
        (RingHom.id (sourceNorm R T) (⟨x, hx⟩ : sourceNorm R T)) :=
      IsIntegral.map_of_comp_eq Algebra.TensorProduct.includeLeftRingHom (RingHom.id _)
        (RingHom.ext fun r => paperTensorMap_tmul_one A R T r) hy
    exact h2.map (IsScalarTower.toAlgHom (R ⊗[A] baseNorm A R T) (sourceNorm R T)
      (sourceAlt R T))
  · have h1 : IsIntegral (sourceNorm R T) x := hx.tower_top
    exact (mem_integralClosure_iff R _).mpr (isIntegral_trans (R := R) (A := sourceNorm R T) x h1)

end

section Literal

open scoped Pcf.Bounding.PaperPPrimaryFibres

/-- **`lem:primary-fibres`, literal affine form, by the paper's proof.** For `q : Spec R → Spec A`
as above there are a dense open `U = D(c)` of `Spec A` and `a ≥ 0` such that for every divisor
`D` of `Spec A` meeting `U` and every divisor `F` of `Spec R` dominating `D` (`F ∩ A = D`),
`v_F(q^* t)` is a power of `p` dividing `p^a`. -/
theorem primaryFibres_affine_paperRoute (p : ℕ) [hp : Fact p.Prime]
    (k : Type u) [Field k] [CharP k p]
    (A R : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra k A]
    [Algebra.FiniteType k A] [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Algebra k R]
    [Algebra A R] [IsScalarTower k A R] [FaithfulSMul A R] [Algebra.FiniteType A R] :
    ∃ c : A, c ≠ 0 ∧ ∃ a : ℕ, ∀ D : PrimeSpectrum A, D.asIdeal.height = 1 →
      D ∈ PrimeSpectrum.basicOpen c → ∀ F : PrimeSpectrum R, F.asIdeal.height = 1 →
        F.asIdeal.under A = D.asIdeal →
          (∃ b, F.asIdeal.ramificationIdx A = p ^ b) ∧ F.asIdeal.ramificationIdx A ∣ p ^ a := by
  obtain ⟨T, -, a, -, -, c, hc0, H⟩ := exists_primaryFibres_paperSquare p k A R
  refine ⟨c, hc0, a, fun D hD hDc F hF hFD => ?_⟩
  haveI : F.asIdeal.LiesOver D.asIdeal := ⟨hFD.symm⟩
  have hc : c ∉ D.asIdeal := hDc
  have hH := H D.asIdeal hD hc F.asIdeal hF inferInstance
  obtain ⟨D', F', -, -, h⟩ := hH
  obtain ⟨b, hb, hbe⟩ := h.2.2.2.2.2.2.2.2
  exact ⟨⟨b, hbe⟩, hbe ▸ pow_dvd_pow p hb⟩

end Literal

end Pcf.Bounding.PaperPPrimaryFibres

#print axioms Pcf.Bounding.PaperPPrimaryFibres.ker_paperTensorMap
#print axioms Pcf.Bounding.PaperPPrimaryFibres.tensorReducedEquivRange
#print axioms Pcf.Bounding.PaperPPrimaryFibres.sourceAlt_mem_fractions_paperTensor
#print axioms Pcf.Bounding.PaperPPrimaryFibres.baseNorm_isNormalization
#print axioms Pcf.Bounding.PaperPPrimaryFibres.sourceNorm_isNormalization_tensorReduced
#print axioms Pcf.Bounding.PaperPPrimaryFibres.primaryFibres_affine_paperRoute
