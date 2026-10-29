/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.FrobeniusLineWeightedBranch
public import Pcf.Bounding.PointRamificationIdx

/-!
# The Frobenius-line map has no index-critical divisor

The invariant line has index one in the actual scheme stalk extension, even
though its residue extension is inseparable. Every other divisor is étale.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.FrobeniusLine

open AlgebraicGeometry CategoryTheory IsLocalRing

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

private theorem ramificationIdx_eq_one_of_map_under {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (q : Ideal S) [q.IsPrime]
    (h : (q.under R).map (algebraMap R S) = q) : q.ramificationIdx R = 1 := by
  rw [Ideal.ramificationIdx_def, IsScalarTower.algebraMap_eq R S (Localization.AtPrime q),
    ← Ideal.map_map, h, Localization.AtPrime.map_eq_maximalIdeal,
    ENat.toNat_eq_iff_eq_natCast, Nat.cast_one, Module.length_eq_one_iff,
    isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def]
  exact IsLocalRing.maximalIdeal.isMaximal _

private theorem localRingHom_ramificationIdx_eq_one_of_map
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime]
    (hf : I = J.comap f) (hmap : I.map f = J) :
    letI := (Localization.localRingHom I J f hf).toAlgebra
    (maximalIdeal (Localization.AtPrime J)).ramificationIdx (Localization.AtPrime I) = 1 := by
  let φ := Localization.localRingHom I J f hf
  letI := φ.toAlgebra
  haveI : IsLocalHom (algebraMap (Localization.AtPrime I) (Localization.AtPrime J)) :=
    show IsLocalHom (Localization.localRingHom I J f hf) from inferInstance
  apply ramificationIdx_eq_one_of_map_under
  have hcomp : φ.comp (algebraMap R (Localization.AtPrime I)) =
      (algebraMap S (Localization.AtPrime J)).comp f := by
    ext x
    exact Localization.localRingHom_to_map I J f hf x
  rw [Ideal.under_def, IsLocalRing.maximalIdeal_comap,
    ← Localization.AtPrime.map_eq_maximalIdeal (I := I), Ideal.map_map]
  change I.map (φ.comp (algebraMap R (Localization.AtPrime I))) = _
  rw [hcomp, ← Ideal.map_map, hmap, Localization.AtPrime.map_eq_maximalIdeal]

variable (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

omit [CharP k p] in
/-- Ramification index one along `H`, measured using the actual scheme stalks. -/
theorem schemeMap_lineDivisor_ramificationIdx :
    Pcf.schemeDivisorRamificationIdx (schemeMap k p) (lineDivisor k) = 1 := by
  let f := (coordinateMap k p).toRingHom
  let q := linePoint k
  let e := Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom f) q
  have hidx := Pcf.ramificationIdx_maximalIdeal_eq_of_ringEquiv
    ((schemeMap k p).stalkMap q).hom
    (Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl)
    (Arrow.leftFunc.mapIso e).commRingCatIsoToRingEquiv
    (Arrow.rightFunc.mapIso e).commRingCatIsoToRingEquiv (by
      exact congrArg CommRingCat.Hom.hom e.hom.w)
  change Pcf.schemeDivisorRamificationIdx (schemeMap k p) (lineDivisor k) = _ at hidx
  rw [hidx]
  apply localRingHom_ramificationIdx_eq_one_of_map
  change ((lineIdeal k).comap f).map f = lineIdeal k
  rw [lineIdeal_comap k p (Fact.out : p.Prime).pos, lineIdeal_map]

local instance indexFinite : IsFinite (schemeMap k p) :=
  schemeMap_finite k p (Fact.out : p.Prime).two_le
local instance indexSurjective : Surjective (schemeMap k p) :=
  schemeMap_surjective k p (Fact.out : p.Prime).two_le

/-- Every integral effective divisor of the actual scheme map has index one.

`paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem schemeMap_divisorRamificationIdx_eq_one
    (d : Pcf.SchemeDivisorPoint (Spec (.of (Plane k)))) :
    Pcf.schemeDivisorRamificationIdx (schemeMap k p) d = 1 := by
  by_cases hd : d = lineDivisor k
  · rw [hd]
    exact schemeMap_lineDivisor_ramificationIdx k p
  · exact (Pcf.schemeDivisorDelta_eq_one_iff _ d).mp
      (Pcf.schemeDivisorDelta_eq_one_of_formallyEtale _ d
        (divisor_stalk_formallyEtale_of_ne_line k p d hd)) |>.1

/-- The index-only critical integral effective divisor locus is empty.

`paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem schemeMap_indexCritical_empty :
    {d : Pcf.SchemeDivisorPoint (Spec (.of (Plane k))) |
      1 < Pcf.schemeDivisorRamificationIdx (schemeMap k p) d} = ∅ := by
  ext d
  simp only [Set.mem_ofPred_eq, schemeMap_divisorRamificationIdx_eq_one,
    lt_self_iff_false, Set.mem_empty_iff_false]

#print axioms schemeMap_lineDivisor_ramificationIdx
#print axioms schemeMap_divisorRamificationIdx_eq_one
#print axioms schemeMap_indexCritical_empty

end Pcf.Examples.PaperP.FrobeniusLine
