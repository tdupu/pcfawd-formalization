/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.DegreeOnlyResidueGeneric
public import Pcf.Examples.PaperP.FrobeniusLineNotAllTheWayDown
public import Pcf.Examples.PaperP.FrobeniusLineResidue
public import Pcf.Examples.PaperP.FrobeniusLineWeightedBranch
public import Pcf.Bounding.PaperPDivisorialSpecialization

/-!
# Degree prime to `p` does not control residue fields

`latex/paper-p.tex`, `sec:prime-to-p`, opening paragraph: monodromy not divisible by `p`
"makes ramification tame and residue fields separable … A condition only on the degree of
the original map would not control residue fields."

For `F : 𝔸²_{x,w} → 𝔸²_{u,v}`, `F^*(u) = x^p + x w`, `F^*(v) = w (x - 1)`:

* the generic degree is `p + 1`, prime to `p` (`DegreeOnlyResidueGeneric`);
* the integral divisor `V(w)` maps onto `V(v)`, and on it `F` restricts to the relative
  Frobenius `x ↦ x^p` of the line (`restriction_scheme_square`, `invariant_line_image`);
* the actual residue-field extension `κ(V(w)) / κ(V(v))`, i.e. `k(x) / k(x^p)`, is purely
  inseparable of degree `p`, hence not separable (`lineResidueMap_not_isSeparable`,
  `lineResidueMap_isPurelyInseparable`, `lineResidueMap_finrank`);
* consequently `F` does not have prime-to-`p` monodromy, by `lem:prime-to-p-restrict`
  (`Pcf.paperP_primeToP_divisorialSpecialization`): `schemeMap_not_isPrimeToPMonodromyMap`.

The ideal `(X₁)` of `Plane k` is `(w)` on the source and `(v)` on the target, so the
line, its closed embedding and its residue model are those of the Frobenius-line example.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.DegreeOnlyResidue

open AlgebraicGeometry CategoryTheory
open Pcf.Examples.PaperP.FrobeniusLine (Plane u v lineIdeal lineEvaluation lineCoordinateMap
  lineCoordinateMap_X lineSchemeMap lineEmbedding lineEvaluation_ker lineCoordinateMap_injective
  lineResidueEquiv lineFunctionFieldMap linePoint lineDivisor canonicalLineToExplicit
  planeStructure)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable (k : Type*) [Field k] (p : ℕ)

/-- On the line `w = 0` the map `F^*` is `x ↦ x^p`: equality of actual algebra maps. -/
theorem restriction_coordinate_square :
    (lineEvaluation k).comp (coordinateMap k p) =
      (lineCoordinateMap k p).comp (lineEvaluation k) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [lineEvaluation, coordinateMap, u, v, lineCoordinateMap_X]

theorem restriction_scheme_square : lineEmbedding k ≫ schemeMap k p =
    lineSchemeMap k p ≫ lineEmbedding k := by
  unfold lineEmbedding schemeMap lineSchemeMap
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun h : Plane k →ₐ[k] Polynomial k =>
    Spec.map (CommRingCat.ofHom h.toRingHom)) (restriction_coordinate_square k p)

/-- The divisor `(w)` pulls back from `(v)`: `(F^*)^{-1}(w) = (v)`. -/
theorem lineIdeal_comap (hp : 0 < p) :
    (lineIdeal k).comap (coordinateMap k p).toRingHom = lineIdeal k := by
  rw [← lineEvaluation_ker]
  ext q
  change lineEvaluation k (coordinateMap k p q) = 0 ↔ lineEvaluation k q = 0
  have h := congrArg (fun h => h q) (restriction_coordinate_square k p)
  change lineEvaluation k (coordinateMap k p q) = lineCoordinateMap k p (lineEvaluation k q) at h
  rw [h]
  exact ⟨fun hq => (lineCoordinateMap_injective k p hp) (by simpa using hq),
    fun hq => by rw [hq, map_zero]⟩

/-- `F` sends the generic point of `V(w)` to the generic point of `V(v)`. -/
theorem schemeMap_linePoint (hp : 0 < p) : schemeMap k p (linePoint k) = linePoint k := by
  apply PrimeSpectrum.ext
  exact lineIdeal_comap k p hp

/-- **`V(w)` maps onto `V(v)`.** -/
theorem invariant_line_image (hp : 2 ≤ p) :
    schemeMap k p '' PrimeSpectrum.zeroLocus (lineIdeal k) =
      PrimeSpectrum.zeroLocus (lineIdeal k) := by
  rw [← FrobeniusLine.lineEmbedding_range, ← Set.range_comp]
  have hfunc : (schemeMap k p) ∘ lineEmbedding k = lineEmbedding k ∘ lineSchemeMap k p :=
    congrArg (fun h => (fun q => h q)) (restriction_scheme_square k p)
  rw [hfunc, Set.range_comp]
  have hsurj := (surjective_iff (lineSchemeMap k p)).mp
    (FrobeniusLine.lineSchemeMap_surjective k p hp)
  rw [hsurj.range_eq, Set.image_univ]

section Residue

variable [Fact p.Prime]

/-- The actual residue-field map `κ(V(v)) → κ(V(w))` induced by `F` at the generic
point of `V(w)`. -/
noncomputable def lineResidueMap :
    (lineIdeal k).ResidueField →ₐ[k] (lineIdeal k).ResidueField :=
  Ideal.ResidueField.mapₐ (lineIdeal k) (lineIdeal k) (coordinateMap k p)
    (lineIdeal_comap k p (Fact.out : p.Prime).pos).symm

@[simp] theorem lineResidueMap_on_plane (q : Plane k) :
    lineResidueMap k p (algebraMap (Plane k) (lineIdeal k).ResidueField q) =
      algebraMap (Plane k) (lineIdeal k).ResidueField (coordinateMap k p q) := by
  exact Ideal.ResidueField.map_algebraMap ..

/-- The residue map is conjugate to the function-field map `x ↦ x^p` of the line. -/
theorem lineResidueMap_conjugation :
    (lineFunctionFieldMap k p).toRingHom.comp (lineResidueEquiv k).toRingHom =
      (lineResidueEquiv k).toRingHom.comp (lineResidueMap k p).toRingHom := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (Plane k ⧸ lineIdeal k))
  apply RingHom.ext
  intro q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  change lineFunctionFieldMap k p
      (lineResidueEquiv k (algebraMap (Plane k) (lineIdeal k).ResidueField r)) =
    lineResidueEquiv k (lineResidueMap k p (algebraMap (Plane k) (lineIdeal k).ResidueField r))
  rw [FrobeniusLine.lineResidueEquiv_on_plane, FrobeniusLine.lineFunctionFieldMap_on_polynomial,
    lineResidueMap_on_plane, FrobeniusLine.lineResidueEquiv_on_plane]
  exact congrArg (algebraMap (Polynomial k) (RatFunc k))
    (congrArg (fun f : Plane k →ₐ[k] Polynomial k => f r)
      (restriction_coordinate_square k p)).symm

variable [CharP k p]

/-- **(c) The residue extension `κ(V(w)) / κ(V(v))` is not separable.** -/
theorem lineResidueMap_not_isSeparable :
    letI := (lineResidueMap k p).toRingHom.toAlgebra
    ¬ Algebra.IsSeparable (lineIdeal k).ResidueField (lineIdeal k).ResidueField := by
  letI := (lineResidueMap k p).toRingHom.toAlgebra
  intro hsep
  letI := hsep
  apply FrobeniusLine.lineFunctionFieldMap_not_isSeparable k p
  letI := (lineFunctionFieldMap k p).toRingHom.toAlgebra
  exact Algebra.IsSeparable.of_equiv_equiv (lineResidueEquiv k) (lineResidueEquiv k)
    (lineResidueMap_conjugation k p)

/-- The residue extension `κ(V(w)) / κ(V(v))` is purely inseparable. -/
theorem lineResidueMap_isPurelyInseparable :
    letI := (lineResidueMap k p).toRingHom.toAlgebra
    IsPurelyInseparable (lineIdeal k).ResidueField (lineIdeal k).ResidueField := by
  letI := (lineResidueMap k p).toRingHom.toAlgebra
  haveI : CharP (lineIdeal k).ResidueField p :=
    charP_of_injective_ringHom (f := (lineResidueEquiv k).symm.toRingHom)
      (lineResidueEquiv k).symm.injective p
  apply (isPurelyInseparable_iff_pow_mem (lineIdeal k).ResidueField p).mpr
  intro x
  let j := lineFunctionFieldMap k p
  letI := j.toRingHom.toAlgebra
  obtain ⟨n, y, hy⟩ := (isPurelyInseparable_iff_pow_mem (RatFunc k) p).mp
    (FrobeniusLine.lineFunctionFieldMap_isPurelyInseparable k p) (lineResidueEquiv k x)
  refine ⟨n, (lineResidueEquiv k).symm y, ?_⟩
  apply (lineResidueEquiv k).injective
  rw [map_pow]
  have h := congrArg (fun f : (lineIdeal k).ResidueField →+* RatFunc k =>
    f ((lineResidueEquiv k).symm y)) (lineResidueMap_conjugation k p)
  change j (lineResidueEquiv k ((lineResidueEquiv k).symm y)) =
    lineResidueEquiv k (lineResidueMap k p ((lineResidueEquiv k).symm y)) at h
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm.trans hy

omit [CharP k p] in
/-- The function-field map `x ↦ x^p` of the line has degree `p`. -/
theorem lineFunctionFieldMap_finrank :
    letI : Module (RatFunc k) (RatFunc k) :=
      (lineFunctionFieldMap k p).toRingHom.toAlgebra.toModule
    Module.finrank (RatFunc k) (RatFunc k) = p := by
  let j := lineFunctionFieldMap k p
  let F := FrobeniusLine.powerSubfield k p
  have hps : Module.finrank F (RatFunc k) = p := FrobeniusLine.powerSubfield_finrank k p
  let inst₁ : Algebra F (RatFunc k) := inferInstance
  have hr : j.range = F.toSubalgebra := by
    rw [← AlgHom.fieldRange_toSubalgebra, FrobeniusLine.lineFunctionFieldMap_fieldRange]
  let i : RatFunc k ≃+* F :=
    (AlgEquiv.ofInjectiveField j).toRingEquiv.trans (Subalgebra.equivOfEq _ _ hr).toRingEquiv
  have hc : (@algebraMap F (RatFunc k) _ _ inst₁).comp i.toRingHom =
      (RingEquiv.refl (RatFunc k)).toRingHom.comp j.toRingHom := by
    ext x
    rfl
  have h := @Algebra.finrank_eq_of_equiv_equiv (RatFunc k) (RatFunc k) _ _ j.toRingHom.toAlgebra
    F (RatFunc k) _ _ inst₁ i (RingEquiv.refl (RatFunc k)) hc
  exact h.trans hps

omit [CharP k p] in
/-- **The residue extension `κ(V(w)) / κ(V(v))` has degree `p`.** -/
theorem lineResidueMap_finrank :
    letI : Module (lineIdeal k).ResidueField (lineIdeal k).ResidueField :=
      (lineResidueMap k p).toRingHom.toAlgebra.toModule
    Module.finrank (lineIdeal k).ResidueField (lineIdeal k).ResidueField = p := by
  letI := (lineResidueMap k p).toRingHom.toAlgebra
  letI := (lineFunctionFieldMap k p).toRingHom.toAlgebra
  exact (Algebra.finrank_eq_of_equiv_equiv (lineResidueEquiv k) (lineResidueEquiv k)
    (lineResidueMap_conjugation k p)).trans (by convert lineFunctionFieldMap_finrank k p)

end Residue

section Monodromy

variable [Fact p.Prime]

local instance schemeMapFinite' : IsFinite (schemeMap k p) :=
  schemeMap_finite k p (Fact.out : p.Prime).pos
local instance schemeMapSurjective' : Surjective (schemeMap k p) :=
  schemeMap_surjective k p (Fact.out : p.Prime).pos
local instance lineFinite : IsFinite (lineSchemeMap k p) :=
  FrobeniusLine.lineSchemeMap_finite k p (Fact.out : p.Prime).two_le
local instance lineSurjective : Surjective (lineSchemeMap k p) :=
  FrobeniusLine.lineSchemeMap_surjective k p (Fact.out : p.Prime).two_le
local instance lineClosed : IsClosedImmersion (lineEmbedding k) :=
  FrobeniusLine.lineEmbedding_isClosedImmersion k
local instance planeNormal : Pcf.IsNormalScheme (Spec (.of (Plane k))) :=
  FrobeniusLine.plane_isNormalScheme k

variable [CharP k p]

/-- The canonical return of `F` on the reduced closure `V(w)` is not generically separable:
it is identified with the relative Frobenius `x ↦ x^p` of the line. -/
theorem lineReturn_not_isGenericallySeparable :
    ¬ Pcf.IsGenericallySeparableSchemeMap (Pcf.pointClosureReturnMap (schemeMap k p)
      (linePoint k) (schemeMap_linePoint k p (Fact.out : p.Prime).pos)) := by
  intro hsep
  apply FrobeniusLine.lineSchemeMap_not_isGenericallySeparable k p
  apply Pcf.isGenericallySeparable_of_finite_commuting_square
    (lineSchemeMap k p)
    (Pcf.pointClosureReturnMap (schemeMap k p) (linePoint k)
      (schemeMap_linePoint k p (Fact.out : p.Prime).pos))
    (canonicalLineToExplicit k) _ hsep
  rw [← cancel_mono (lineEmbedding k), Category.assoc,
    FrobeniusLine.canonicalLineToExplicit_embedding,
    Pcf.pointClosureReturnMap, Pcf.pointClosureSubschemeMap_subschemeι,
    Category.assoc, ← restriction_scheme_square,
    FrobeniusLine.canonicalLineToExplicit_embedding_assoc]

private theorem not_primeToP_closureMap (y : Spec (.of (Plane k)))
    (hy : schemeMap k p (linePoint k) = y)
    [IsFinite (Pcf.pointClosureSubschemeMap (schemeMap k p) (linePoint k) y hy)]
    [IsDominant (Pcf.pointClosureSubschemeMap (schemeMap k p) (linePoint k) y hy)]
    (h : Pcf.IsPrimeToPMonodromyMap p
      (Pcf.pointClosureSubschemeMap (schemeMap k p) (linePoint k) y hy)) : False := by
  obtain rfl : y = linePoint k := hy.symm.trans (schemeMap_linePoint k p (Fact.out : p.Prime).pos)
  apply lineReturn_not_isGenericallySeparable k p
  exact Pcf.isGenericallySeparable_of_isPrimeToPMonodromyMap p _ h

/-- **(d) `F` does not have prime-to-`p` monodromy.** Otherwise `lem:prime-to-p-restrict`
would make the residue extension along `V(w)` separable. -/
theorem schemeMap_not_isPrimeToPMonodromyMap :
    ¬ Pcf.IsPrimeToPMonodromyMap p (schemeMap k p) := by
  intro hmono
  have h := (Pcf.paperP_primeToP_divisorialSpecialization p (Fact.out : p.Prime) k
    (planeStructure k) (schemeMap k p) hmono (lineDivisor k)).2
  letI := Pcf.pointClosureSubschemeMap_isFinite (schemeMap k p) (linePoint k)
    (schemeMap k p (linePoint k)) rfl
  letI := Pcf.pointClosureSubschemeMap_isDominant (schemeMap k p) (linePoint k)
    (schemeMap k p (linePoint k)) rfl
  exact not_primeToP_closureMap k p _ rfl h

/-- **`paper-p.tex`, `sec:prime-to-p`: a degree condition does not control residue
fields.** The map `F` has generic degree `p + 1`, prime to `p`; the integral divisor
`V(w)` maps onto `V(v)` with purely inseparable residue extension of degree `p`; and so
`F` does not have prime-to-`p` monodromy. -/
theorem degreeOnly_does_not_control_residueFields :
    (letI := ((schemeMap k p).stalkMap (genericPoint (Spec (.of (Plane k))))).hom.toAlgebra;
      Module.finrank
        ((Spec (.of (Plane k))).presheaf.stalk
          (schemeMap k p (genericPoint (Spec (.of (Plane k))))))
        ((Spec (.of (Plane k))).presheaf.stalk (genericPoint (Spec (.of (Plane k))))) = p + 1) ∧
    Nat.Coprime (p + 1) p ∧
    schemeMap k p (linePoint k) = linePoint k ∧
    schemeMap k p '' PrimeSpectrum.zeroLocus (lineIdeal k) =
      PrimeSpectrum.zeroLocus (lineIdeal k) ∧
    (letI := (lineResidueMap k p).toRingHom.toAlgebra;
      IsPurelyInseparable (lineIdeal k).ResidueField (lineIdeal k).ResidueField ∧
      (letI : Module (lineIdeal k).ResidueField (lineIdeal k).ResidueField :=
        (lineResidueMap k p).toRingHom.toAlgebra.toModule;
        Module.finrank (lineIdeal k).ResidueField (lineIdeal k).ResidueField = p) ∧
      ¬ Algebra.IsSeparable (lineIdeal k).ResidueField (lineIdeal k).ResidueField) ∧
    ¬ Pcf.IsPrimeToPMonodromyMap p (schemeMap k p) :=
  ⟨schemeMap_genericDegree k p (Fact.out : p.Prime).pos,
    Nat.coprime_self_add_left.mpr (Nat.coprime_one_left p),
    schemeMap_linePoint k p (Fact.out : p.Prime).pos,
    invariant_line_image k p (Fact.out : p.Prime).two_le,
    ⟨lineResidueMap_isPurelyInseparable k p, lineResidueMap_finrank k p,
      lineResidueMap_not_isSeparable k p⟩,
    schemeMap_not_isPrimeToPMonodromyMap k p⟩

end Monodromy

#print axioms restriction_scheme_square
#print axioms invariant_line_image
#print axioms lineResidueMap_not_isSeparable
#print axioms lineResidueMap_isPurelyInseparable
#print axioms lineResidueMap_finrank
#print axioms lineReturn_not_isGenericallySeparable
#print axioms schemeMap_not_isPrimeToPMonodromyMap
#print axioms degreeOnly_does_not_control_residueFields

end Pcf.Examples.PaperP.DegreeOnlyResidue
