/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemePrimaryDeltaTransfer

/-!
# Residue fields on affine charts of the primary normalization

The local δ calculation in `paper-p.tex`, Lemma `lem:pcf-transfer-charp`,
uses residue fields of affine primes. Here these are identified with the
residue fields of actual scheme points, respecting evaluation of sections.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

set_option linter.style.haveILetI false

/-- The residue field of an affine prime is the residue field of the
corresponding point of the scheme. -/
def schemeAffineResidueFieldEquiv
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) :
    let p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    p.ResidueField ≃+* X.residueField x := by
  let xU : U := ⟨x, hx⟩
  let p := (hU.primeIdealOf xU).asIdeal
  letI : Algebra Γ(X, U) (X.presheaf.stalk (xU : X)) :=
    X.presheaf.algebra_section_stalk xU
  letI : IsLocalization.AtPrime (X.presheaf.stalk (xU : X)) p :=
    hU.isLocalization_stalk xU
  exact IsLocalRing.ResidueField.mapEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      (X.presheaf.stalk (xU : X))).toRingEquiv

/-- The affine-prime residue-field equivalence sends reduction of a
section to its evaluation at the scheme point. -/
theorem schemeAffineResidueFieldEquiv_algebraMap
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) (a : Γ(X, U)) :
    let p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    schemeAffineResidueFieldEquiv X U hU x hx
      (algebraMap Γ(X, U) p.ResidueField a) =
      X.evaluation U x hx a := by
  let xU : U := ⟨x, hx⟩
  let p := (hU.primeIdealOf xU).asIdeal
  letI : Algebra Γ(X, U) (X.presheaf.stalk (xU : X)) :=
    X.presheaf.algebra_section_stalk xU
  letI : IsLocalization.AtPrime (X.presheaf.stalk (xU : X)) p :=
    hU.isLocalization_stalk xU
  let e := (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      (X.presheaf.stalk (xU : X))).toRingEquiv
  letI : IsLocalHom e.toRingHom := IsLocalHom.of_surjective _ e.surjective
  change IsLocalRing.ResidueField.map
    e.toRingHom
      (algebraMap Γ(X, U) p.ResidueField a) =
    X.evaluation U x hx a
  have halg : algebraMap Γ(X, U) p.ResidueField a =
      IsLocalRing.residue (Localization.AtPrime p)
        (algebraMap Γ(X, U) (Localization.AtPrime p) a) := rfl
  rw [halg]
  rw [IsLocalRing.ResidueField.map_residue]
  change IsLocalRing.residue (X.presheaf.stalk x)
    ((IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      (X.presheaf.stalk x)) (algebraMap Γ(X, U) (Localization.AtPrime p) a)) =
    IsLocalRing.residue (X.presheaf.stalk x)
      ((X.presheaf.germ U x hx).hom a)
  rw [AlgEquiv.commutes]
  rfl

/-- The affine-prime residue map agrees with the actual residue-field map
of a finite scheme morphism after the canonical affine identifications. -/
theorem schemeAffineResidueFieldEquiv_naturality_of_finite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (U : Y.affineOpens) (x : X) (hx : f x ∈ (U : Y.Opens)) :
    let V := finitePreimageAffine f U
    let p := (U.2.primeIdealOf ⟨f x, hx⟩).asIdeal
    let q := (V.2.primeIdealOf ⟨x, hx⟩).asIdeal
    let hcontract : p = q.comap (f.appLE U V le_rfl).hom := by
      simpa only [PrimeSpectrum.comap_asIdeal] using (congrArg PrimeSpectrum.asIdeal
        (IsAffineOpen.comap_primeIdealOf_appLE (U : Y.Opens) U.2
          (V : X.Opens) V.2 le_rfl hx)).symm
    (f.residueFieldMap x).hom.comp
      (schemeAffineResidueFieldEquiv Y U U.2 (f x) hx).toRingHom =
      (schemeAffineResidueFieldEquiv X V V.2 x hx).toRingHom.comp
        (Ideal.ResidueField.map p q (f.appLE U V le_rfl).hom hcontract) := by
  let V := finitePreimageAffine f U
  let p := (U.2.primeIdealOf ⟨f x, hx⟩).asIdeal
  let q := (V.2.primeIdealOf ⟨x, hx⟩).asIdeal
  let hcontract : p = q.comap (f.appLE U V le_rfl).hom := by
    simpa only [PrimeSpectrum.comap_asIdeal] using (congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE (U : Y.Opens) U.2
        (V : X.Opens) V.2 le_rfl hx)).symm
  apply Ideal.ResidueField.ringHom_ext
  apply RingHom.ext
  intro a
  change (f.residueFieldMap x).hom
      (schemeAffineResidueFieldEquiv Y U U.2 (f x) hx
        (algebraMap Γ(Y, U) p.ResidueField a)) =
    schemeAffineResidueFieldEquiv X V V.2 x hx
      (Ideal.ResidueField.map p q (f.appLE U V le_rfl).hom hcontract
        (algebraMap Γ(Y, U) p.ResidueField a))
  have hbase : schemeAffineResidueFieldEquiv Y U U.2 (f x) hx
      (algebraMap Γ(Y, U) p.ResidueField a) = Y.evaluation U (f x) hx a := by
    exact schemeAffineResidueFieldEquiv_algebraMap Y U U.2 (f x) hx a
  have hsource : schemeAffineResidueFieldEquiv X V V.2 x hx
      (algebraMap Γ(X, V) q.ResidueField ((f.appLE U V le_rfl).hom a)) =
      X.evaluation V x hx ((f.appLE U V le_rfl).hom a) := by
    exact schemeAffineResidueFieldEquiv_algebraMap X V V.2 x hx _
  calc
    (f.residueFieldMap x).hom
        (schemeAffineResidueFieldEquiv Y U U.2 (f x) hx
          (algebraMap Γ(Y, U) p.ResidueField a)) =
        (f.residueFieldMap x).hom (Y.evaluation U (f x) hx a) := by rw [hbase]
    _ = X.evaluation (f ⁻¹ᵁ (U : Y.Opens)) x hx ((f.app U).hom a) :=
      Scheme.evaluation_naturality_apply f x hx a
    _ = X.evaluation V x hx ((f.appLE U V le_rfl).hom a) := by
      change X.evaluation (f ⁻¹ᵁ (U : Y.Opens)) x hx ((f.app U).hom a) =
        X.evaluation (f ⁻¹ᵁ (U : Y.Opens)) x hx
          ((f.appLE U (f ⁻¹ᵁ (U : Y.Opens)) le_rfl).hom a)
      rw [f.appLE_eq_app]
    _ = schemeAffineResidueFieldEquiv X V V.2 x hx
          (algebraMap Γ(X, V) q.ResidueField ((f.appLE U V le_rfl).hom a)) :=
      hsource.symm
    _ = schemeAffineResidueFieldEquiv X V V.2 x hx
          (Ideal.ResidueField.map p q (f.appLE U V le_rfl).hom hcontract
            (algebraMap Γ(Y, U) p.ResidueField a)) := by
      rw [Ideal.ResidueField.map_algebraMap]

/-- A commuting square of field isomorphisms preserves pure inseparability
and its numerical inseparable degree. -/
theorem finInsepDegree_eq_of_ringEquiv_square_of_purelyInseparable
    {F E F' E' : Type*}
    [Field F] [Field E] [Algebra F E]
    [Field F'] [Field E'] [Algebra F' E']
    (i : F ≃+* F') (j : E ≃+* E')
    (hc : (algebraMap F' E').comp i.toRingHom =
      j.toRingHom.comp (algebraMap F E))
    [IsPurelyInseparable F E] :
    IsPurelyInseparable F' E' ∧
      Field.finInsepDegree F E = Field.finInsepDegree F' E' := by
  let q := ringExpChar F
  have hq : ExpChar F q := inferInstance
  have hq' : ExpChar F' q :=
    expChar_of_injective_ringHom i.toRingHom.injective q
  have hpure : IsPurelyInseparable F' E' := by
    apply (isPurelyInseparable_iff_pow_mem F' q).2
    intro y
    obtain ⟨x, rfl⟩ := j.surjective y
    obtain ⟨n, a, ha⟩ :=
      (IsPurelyInseparable.pow_mem F q x)
    refine ⟨n, i a, ?_⟩
    change algebraMap F' E' (i a) = (j x) ^ q ^ n
    rw [← map_pow, ← ha]
    exact congrArg (fun h : F →+* E' => h a) hc
  letI : IsPurelyInseparable F' E' := hpure
  refine ⟨hpure, ?_⟩
  rw [IsPurelyInseparable.finInsepDegree_eq F E,
    IsPurelyInseparable.finInsepDegree_eq F' E']
  exact Algebra.finrank_eq_of_equiv_equiv i j hc

/-- For a finite scheme morphism, pure inseparability and its degree can be
computed on any affine chart containing the point. -/
theorem schemeResidueField_finInsepDegree_eq_affine_of_purelyInseparable
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (U : Y.affineOpens) (x : X) (hx : f x ∈ (U : Y.Opens)) :
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
    IsPurelyInseparable p.ResidueField q.ResidueField →
      IsPurelyInseparable (Y.residueField (f x)) (X.residueField x) ∧
      Field.finInsepDegree p.ResidueField q.ResidueField =
        Field.finInsepDegree (Y.residueField (f x)) (X.residueField x) := by
  dsimp only
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
  intro hpure
  letI : IsPurelyInseparable p.ResidueField q.ResidueField := hpure
  let i := schemeAffineResidueFieldEquiv Y U U.2 (f x) hx
  let j := schemeAffineResidueFieldEquiv X V V.2 x hx
  have hc : (algebraMap (Y.residueField (f x)) (X.residueField x)).comp
        i.toRingHom = j.toRingHom.comp
          (algebraMap p.ResidueField q.ResidueField) := by
    exact schemeAffineResidueFieldEquiv_naturality_of_finite f U x hx
  exact finInsepDegree_eq_of_ringEquiv_square_of_purelyInseparable i j hc

#print axioms schemeAffineResidueFieldEquiv
#print axioms schemeAffineResidueFieldEquiv_algebraMap
#print axioms schemeAffineResidueFieldEquiv_naturality_of_finite
#print axioms finInsepDegree_eq_of_ringEquiv_square_of_purelyInseparable
#print axioms schemeResidueField_finInsepDegree_eq_affine_of_purelyInseparable

end
end Pcf
