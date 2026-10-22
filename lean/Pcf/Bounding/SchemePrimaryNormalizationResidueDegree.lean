/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemePrimaryLocalizedDelta

/-!
# Inseparable residue degree on a normalization chart

The characteristic-power root property of the actual affine
normalization computes its scheme residue degree in the integral
closure chart. This is the residue factor in the δ identity of
`paper-p.tex`, Lemma `lem:pcf-transfer-charp`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

set_option linter.style.haveILetI false

/-- On a finite affine preimage with the characteristic-power root
property, the scheme residue extension has the same inseparable
degree as the corresponding extension of affine-prime residue fields. -/
theorem finiteSchemeMap_residueInsepDegree_eq_affine_of_pow_mem
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (U : Y.affineOpens) (x : X) (hx : f x ∈ (U : Y.Opens))
    (pchar : ℕ)
    [ExpChar ((U.2.primeIdealOf ⟨f x, hx⟩).asIdeal).ResidueField pchar]
    (hroot : ∀ s : Γ(X, finitePreimageAffine f U),
      ∃ (n : ℕ) (r : Γ(Y, U)),
        s ^ (pchar ^ n) = (f.appLE U (finitePreimageAffine f U) le_rfl).hom r) :
    let V := finitePreimageAffine f U
    let p := (U.2.primeIdealOf ⟨f x, hx⟩).asIdeal
    let q := (V.2.primeIdealOf ⟨x, hx⟩).asIdeal
    let hcontract : p = q.comap (f.appLE U V le_rfl).hom := by
      simpa only [PrimeSpectrum.comap_asIdeal] using (congrArg PrimeSpectrum.asIdeal
        (IsAffineOpen.comap_primeIdealOf_appLE (U : Y.Opens) U.2
          (V : X.Opens) V.2 le_rfl hx)).symm
    letI : Algebra p.ResidueField q.ResidueField :=
      (Ideal.ResidueField.map p q (f.appLE U V le_rfl).hom hcontract).toAlgebra
    letI : Algebra (Y.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    Field.finInsepDegree p.ResidueField q.ResidueField =
      Field.finInsepDegree (Y.residueField (f x)) (X.residueField x) := by
  dsimp only
  let V := finitePreimageAffine f U
  letI : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V le_rfl).hom.toAlgebra
  let p := (U.2.primeIdealOf ⟨f x, hx⟩).asIdeal
  let q := (V.2.primeIdealOf ⟨x, hx⟩).asIdeal
  let hcontract : p = q.comap (f.appLE U V le_rfl).hom := by
    simpa only [PrimeSpectrum.comap_asIdeal] using (congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE (U : Y.Opens) U.2
        (V : X.Opens) V.2 le_rfl hx)).symm
  letI : q.LiesOver p := ⟨hcontract⟩
  letI := Localization.AtPrime.algebraOfLiesOver p q
  have hpure : IsPurelyInseparable p.ResidueField q.ResidueField :=
    Bounding.PrimaryFibres.residueField_isPurelyInseparable_of_pow_mem_base_at_prime
      Γ(Y, U) Γ(X, V) p q pchar hroot
  let alg₀ : Algebra p.ResidueField q.ResidueField := inferInstance
  let alg₁ : Algebra p.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map p q (f.appLE U V le_rfl).hom hcontract).toAlgebra
  have heq : alg₀ = alg₁ := by
    apply Algebra.algebra_ext
    intro r
    rfl
  letI : Algebra p.ResidueField q.ResidueField := alg₁
  have hpure' : IsPurelyInseparable p.ResidueField q.ResidueField := by
    change @IsPurelyInseparable p.ResidueField q.ResidueField _ _ alg₁
    rw [← heq]
    exact hpure
  exact (schemeResidueField_finInsepDegree_eq_affine_of_purelyInseparable
    f U x hx hpure').2

/-- The actual finite normalization in a purely inseparable function-field
extension has the same residue inseparable degree at a scheme point as on
its canonical affine preimage chart. -/
theorem schemeFieldExtensionNormalization_residueInsepDegree_eq_affine
    (X : Scheme.{u}) [IsIntegral X] [IsNormalScheme X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    [IsPurelyInseparable X.functionField L]
    [IsFinite (schemeFieldExtensionInclusion X L).fromNormalization]
    (U : X.affineOpens) [Nonempty (U : X.Opens)]
    (y : (schemeFieldExtensionInclusion X L).normalization)
    (hy : (schemeFieldExtensionInclusion X L).fromNormalization y ∈ (U : X.Opens))
    (pchar : ℕ) [ExpChar X.functionField pchar]
    [ExpChar ((U.2.primeIdealOf ⟨(schemeFieldExtensionInclusion X L).fromNormalization y,
      hy⟩).asIdeal).ResidueField pchar] :
    let g := (schemeFieldExtensionInclusion X L).fromNormalization
    let V := finitePreimageAffine g U
    let p := (U.2.primeIdealOf ⟨g y, hy⟩).asIdeal
    let q := (V.2.primeIdealOf ⟨y, hy⟩).asIdeal
    let hcontract : p = q.comap (g.appLE U V le_rfl).hom := by
      simpa only [PrimeSpectrum.comap_asIdeal] using (congrArg PrimeSpectrum.asIdeal
        (IsAffineOpen.comap_primeIdealOf_appLE (U : X.Opens) U.2
          (V : (schemeFieldExtensionInclusion X L).normalization.Opens)
          V.2 le_rfl hy)).symm
    letI : Algebra p.ResidueField q.ResidueField :=
      (Ideal.ResidueField.map p q (g.appLE U V le_rfl).hom hcontract).toAlgebra
    letI : Algebra (X.residueField (g y))
      ((schemeFieldExtensionInclusion X L).normalization.residueField y) :=
      (g.residueFieldMap y).hom.toAlgebra
    Field.finInsepDegree p.ResidueField q.ResidueField =
      Field.finInsepDegree (X.residueField (g y))
        ((schemeFieldExtensionInclusion X L).normalization.residueField y) := by
  let g := (schemeFieldExtensionInclusion X L).fromNormalization
  have hroot : ∀ s : Γ((schemeFieldExtensionInclusion X L).normalization,
      finitePreimageAffine g U),
      ∃ (n : ℕ) (r : Γ(X, U)),
        s ^ (pchar ^ n) =
          (g.appLE U (finitePreimageAffine g U) le_rfl).hom r := by
    intro s
    obtain ⟨n, r, hr⟩ :=
      schemeFieldExtensionNormalization_affine_pow_mem X L U pchar s
    refine ⟨n, r, ?_⟩
    rw [← g.appLE_eq_app] at hr
    exact hr
  exact finiteSchemeMap_residueInsepDegree_eq_affine_of_pow_mem
    g U y hy pchar hroot

#print axioms finiteSchemeMap_residueInsepDegree_eq_affine_of_pow_mem
#print axioms schemeFieldExtensionNormalization_residueInsepDegree_eq_affine

end
end Pcf
