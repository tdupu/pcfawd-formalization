/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemePrimaryDeltaEquality
public import Pcf.Bounding.PrimaryResidueAllPrimes

/-!
# Purely inseparable residue fields of a primary normalization

Power roots in an affine cover descend to residue fields at arbitrary
scheme points. This is the residue-field part of the local `δ=q` identity
in `paper-p.tex`, Lemma `lem:pcf-transfer-charp`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

set_option linter.style.haveILetI false

/-- If a finite morphism has the power-root property on an affine preimage,
the actual scheme residue-field extension at every point above that chart
is purely inseparable. -/
theorem finiteSchemeMap_residueField_isPurelyInseparable_of_affine_pow_mem
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (U : Y.affineOpens) (x : X) (hx : f x ∈ (U : Y.Opens))
    (pchar : ℕ)
    [ExpChar ((U.2.primeIdealOf ⟨f x, hx⟩).asIdeal).ResidueField pchar]
    (hroot : ∀ s : Γ(X, finitePreimageAffine f U),
      ∃ (n : ℕ) (r : Γ(Y, U)),
        s ^ (pchar ^ n) = (f.appLE U (finitePreimageAffine f U) le_rfl).hom r) :
    letI : Algebra (Y.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    IsPurelyInseparable (Y.residueField (f x)) (X.residueField x) := by
  let V := finitePreimageAffine f U
  let R := Γ(Y, U)
  let S := Γ(X, V)
  letI : Algebra R S := (f.appLE U V le_rfl).hom.toAlgebra
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
      R S p q pchar hroot
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
    f U x hx hpure').1

#print axioms finiteSchemeMap_residueField_isPurelyInseparable_of_affine_pow_mem

end
end Pcf
