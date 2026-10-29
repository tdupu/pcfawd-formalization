/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Degree-multiplying maps of homogeneous localizations

The homogeneous substitution in `paper-p.tex`, Lemma `lem:jacobian`, sends
degree `m` to degree `d*m`. Fractions with numerator and denominator of the
same degree still map to degree-zero fractions. This is the localization
infrastructure needed for its global projective scheme morphism.
-/

@[expose] public section
namespace Pcf
open HomogeneousLocalization
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A B σ τ : Type*} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : A →+* B) (d : ℕ) (hf : ∀ m a, a ∈ 𝒜 m → f a ∈ ℬ (d * m))
  {P : Submonoid A} {Q : Submonoid B} (hPQ : P ≤ Q.comap f)

/-- Apply a degree-multiplying ring map to both entries of a homogeneous
fraction, multiplying the recorded common degree by `d`. -/
def paperPDegreeMapFraction (c : NumDenSameDeg 𝒜 P) : NumDenSameDeg ℬ Q where
  deg := d * c.deg
  num := ⟨f c.num, hf _ _ c.num.2⟩
  den := ⟨f c.den, hf _ _ c.den.2⟩
  den_mem := hPQ c.den_mem

/-- The induced map on degree-zero localized fractions. -/
def paperPDegreeLocalizationMapFun :
    HomogeneousLocalization 𝒜 P → HomogeneousLocalization ℬ Q :=
  Quotient.map' (paperPDegreeMapFraction f d hf hPQ)
    fun x y (e : x.embedding = y.embedding) => by
      apply_fun IsLocalization.map (Localization Q) f hPQ at e
      simp_rw [NumDenSameDeg.embedding, Localization.mk_eq_mk',
        IsLocalization.map_mk', ← Localization.mk_eq_mk'] at e
      exact e

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
@[simp] theorem paperPDegreeLocalizationMapFun_mk (c : NumDenSameDeg 𝒜 P) :
    paperPDegreeLocalizationMapFun f d hf hPQ (mk c) =
      mk (paperPDegreeMapFraction f d hf hPQ c) := rfl

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- On underlying ordinary localizations this is the usual localization map. -/
@[simp] theorem paperPDegreeLocalizationMapFun_val
    (z : HomogeneousLocalization 𝒜 P) :
    (paperPDegreeLocalizationMapFun f d hf hPQ z).val =
      IsLocalization.map (Localization Q) f hPQ z.val := by
  obtain ⟨c, rfl⟩ := z.mk_surjective
  simp only [paperPDegreeLocalizationMapFun_mk, val_mk, paperPDegreeMapFraction,
    Localization.mk_eq_mk', IsLocalization.map_mk']

/-- A degree-multiplying ring map induces a ring homomorphism on degree-zero
homogeneous localizations. -/
def paperPDegreeLocalizationMap :
    HomogeneousLocalization 𝒜 P →+* HomogeneousLocalization ℬ Q where
  toFun := paperPDegreeLocalizationMapFun f d hf hPQ
  map_zero' := by apply val_injective; simp
  map_one' := by apply val_injective; simp
  map_add' x y := by apply val_injective; simp
  map_mul' x y := by apply val_injective; simp

@[simp] theorem paperPDegreeLocalizationMap_mk (c : NumDenSameDeg 𝒜 P) :
    paperPDegreeLocalizationMap f d hf hPQ (mk c) =
      mk (paperPDegreeMapFraction f d hf hPQ c) := rfl

@[simp] theorem paperPDegreeLocalizationMap_val (z : HomogeneousLocalization 𝒜 P) :
    (paperPDegreeLocalizationMap f d hf hPQ z).val =
      IsLocalization.map (Localization Q) f hPQ z.val :=
  paperPDegreeLocalizationMapFun_val f d hf hPQ z

/-- The corresponding local homomorphism at prime ideals. -/
noncomputable def paperPDegreeLocalRingHom (I : Ideal A) [I.IsPrime]
    (J : Ideal B) [J.IsPrime] (hIJ : I = J.comap f) :
    AtPrime 𝒜 I →+* AtPrime ℬ J :=
  paperPDegreeLocalizationMap f d hf
    (Localization.le_comap_primeCompl_iff.mpr (hIJ ▸ le_rfl))

@[simp] theorem paperPDegreeLocalRingHom_val (I : Ideal A) [I.IsPrime]
    (J : Ideal B) [J.IsPrime] (hIJ : I = J.comap f) (z : AtPrime 𝒜 I) :
    (paperPDegreeLocalRingHom f d hf I J hIJ z).val =
      Localization.localRingHom I J f hIJ z.val :=
  paperPDegreeLocalizationMap_val f d hf _ z

instance paperPDegreeLocalRingHom_isLocalHom (I : Ideal A) [I.IsPrime]
    (J : Ideal B) [J.IsPrime] (hIJ : I = J.comap f) :
    IsLocalHom (paperPDegreeLocalRingHom f d hf I J hIJ) where
  map_nonunit z hz := by
    rw [← isUnit_iff_isUnit_val] at hz ⊢
    rw [paperPDegreeLocalRingHom_val] at hz
    exact IsLocalHom.map_nonunit _ hz

#print axioms paperPDegreeLocalizationMap
#print axioms paperPDegreeLocalRingHom
#print axioms paperPDegreeLocalRingHom_isLocalHom
end Pcf
