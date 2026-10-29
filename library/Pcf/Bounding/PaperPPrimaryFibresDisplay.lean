/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBoundBlowupRamificationSquare

/-!
# The valuation display in the proof of `lem:primary-fibres`

`paper-p.tex`, proof of Lemma `lem:primary-fibres`:

> the fibre at `F'` is reduced, so `v_{F'}(q'^* t') = 1` for a local equation `t'` of `D'`.
> Comparing orders of `t` around the square gives
> `e(F'/F) v_F(q^* t) = e(D'/D) v_{F'}(q'^* t') = e(D'/D)`.

Encoding. For a dominant map `φ` and a divisor `F` over a divisor `D` of a normal target,
`v_F(φ^* t)` for a uniformizer `t` of the DVR `𝒪_D` is the length of `𝒪_F / 𝔪_D 𝒪_F`, i.e.
`schemeDivisorRamificationIdx φ F`. The square is the actual commutative square
```
E' --πE--> E
|q'        |q
v          v
B' --πB--> B
```
of integral normal schemes. "The fibre at `F'` is reduced" is the local statement
`𝒪_{E',F'} / 𝔪_{D'} 𝒪_{E',F'}` reduced (the local ring of the fibre `E'_{D'}` at `F'`).

Not done here: the construction of the specific square (`B'` = normalization of `B` in
`K'`, `E'` = normalization of `(E ×_B B')_red`) and the spreading-out of geometric
reducedness (Stacks `0578`); the display is proved for every such actual square.
-/

@[expose] public section

namespace Pcf.Bounding

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u
noncomputable section

set_option linter.style.haveILetI false

/-- In a DVR, a nonzero radical ideal contained in the maximal ideal is the maximal ideal. -/
theorem dvr_eq_maximalIdeal_of_isRadical {T : Type*} [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] (I : Ideal T) (h0 : I ≠ ⊥) (htop : I ≠ ⊤)
    (hrad : I.IsRadical) : I = maximalIdeal T := by
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal T
    (IsDiscreteValuationRing.toIsPrincipalIdealRing.principal _) I h0
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact htop (by simpa using hn)
  rw [← hrad.radical, hn, Ideal.radical_pow _ hn0]
  exact (inferInstance : (maximalIdeal T).IsPrime).radical

/-- **Reduced local fibre ⇒ multiplicity one.** If the local ring of the fibre of `φ`
at a divisor `F` (over a divisor of a normal target) is reduced, then
`v_F(φ^* t) = 1`. No finiteness of `φ` is assumed. -/
theorem schemeDivisorRamificationIdx_eq_one_of_reduced_localFibre
    {E' B' : Scheme.{u}} (φ : E' ⟶ B') [IsDominant φ] [QuasiCompact φ]
    [IsIntegral E'] [IsIntegral B'] [IsLocallyNoetherian E'] [IsLocallyNoetherian B']
    [IsNormalScheme E'] [IsNormalScheme B']
    (F' : SchemeDivisorPoint E') (hD' : Order.coheight (φ F'.1) = 1)
    (hred : letI := (φ.stalkMap F'.1).hom.toAlgebra
      _root_.IsReduced (E'.presheaf.stalk F'.1 ⧸
        (maximalIdeal (B'.presheaf.stalk (φ F'.1))).map
          (algebraMap (B'.presheaf.stalk (φ F'.1)) (E'.presheaf.stalk F'.1)))) :
    schemeDivisorRamificationIdx φ F' = 1 := by
  let S := B'.presheaf.stalk (φ F'.1)
  let T := E'.presheaf.stalk F'.1
  letI : Algebra S T := (φ.stalkMap F'.1).hom.toAlgebra
  letI : IsLocalHom (algebraMap S T) :=
    show IsLocalHom (φ.stalkMap F'.1).hom from inferInstance
  let D' : SchemeDivisorPoint B' := ⟨φ F'.1, hD'⟩
  letI : IsDiscreteValuationRing S := D'.stalk_isDiscreteValuationRing
  letI : IsDiscreteValuationRing T := F'.stalk_isDiscreteValuationRing
  have hinj : Function.Injective (algebraMap S T) :=
    stalkMap_injective_of_dominant_integral φ F'.1
  let I : Ideal T := (maximalIdeal S).map (algebraMap S T)
  have h0 : I ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
    exact IsDiscreteValuationRing.not_a_field S
  have hle : I ≤ maximalIdeal T :=
    Ideal.map_le_iff_le_comap.mpr (fun x hx => map_nonunit _ x hx)
  have htop : I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal T).ne_top hle
  have hrad : I.IsRadical := (Ideal.isRadical_iff_quotient_reduced I).mpr hred
  have hI : I = maximalIdeal T := dvr_eq_maximalIdeal_of_isRadical I h0 htop hrad
  change (maximalIdeal T).ramificationIdx S = 1
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count (maximalIdeal S)
    (maximalIdeal T) h0]
  change Multiset.count (maximalIdeal T) (UniqueFactorizationMonoid.normalizedFactors I) = 1
  rw [hI, UniqueFactorizationMonoid.normalizedFactors_irreducible
    ((Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field T)
      inferInstance).irreducible), normalize_eq, Multiset.count_singleton_self]

/-- **The display of `lem:primary-fibres`.** For an actual commutative square
`πE ≫ q = q' ≫ πB` (`E' → E → B` and `E' → B' → B`) of integral normal schemes, a divisor
`F'` of `E'` over divisors `F` of `E` and `D'` of `B'`, with reduced local fibre of `q'` at
`F'`:
`e(F'/F) · v_F(q^* t) = e(D'/D) · v_{F'}(q'^* t') = e(D'/D)`. -/
theorem primaryFibres_valuation_display
    {E' E B' B : Scheme.{u}}
    (q' : E' ⟶ B') (πE : E' ⟶ E) (πB : B' ⟶ B) (q : E ⟶ B)
    [IsDominant q'] [QuasiCompact q'] [IsDominant πE] [QuasiCompact πE]
    [IsIntegral E'] [IsIntegral E] [IsIntegral B']
    [IsLocallyNoetherian E'] [IsLocallyNoetherian E] [IsLocallyNoetherian B']
    [IsNormalScheme E'] [IsNormalScheme E] [IsNormalScheme B']
    (hcomm : q' ≫ πB = πE ≫ q)
    (F' : SchemeDivisorPoint E')
    (hD' : Order.coheight (q' F'.1) = 1)
    (hF : Order.coheight (πE F'.1) = 1)
    (hred : letI := (q'.stalkMap F'.1).hom.toAlgebra
      _root_.IsReduced (E'.presheaf.stalk F'.1 ⧸
        (maximalIdeal (B'.presheaf.stalk (q' F'.1))).map
          (algebraMap (B'.presheaf.stalk (q' F'.1)) (E'.presheaf.stalk F'.1)))) :
    schemeDivisorRamificationIdx πE F' * schemeDivisorRamificationIdx q ⟨πE F'.1, hF⟩ =
        schemeDivisorRamificationIdx πB ⟨q' F'.1, hD'⟩ * schemeDivisorRamificationIdx q' F' ∧
      schemeDivisorRamificationIdx πB ⟨q' F'.1, hD'⟩ * schemeDivisorRamificationIdx q' F' =
        schemeDivisorRamificationIdx πB ⟨q' F'.1, hD'⟩ := by
  have hsq := schemeDivisorRamificationIdx_square q' πE πB q hcomm F' hD' hF
  have h1 := schemeDivisorRamificationIdx_eq_one_of_reduced_localFibre q' F' hD' hred
  refine ⟨?_, by rw [h1, mul_one]⟩
  rw [hsq, mul_comm]

/-- Consequence used next in the proof: `v_F(q^* t)` divides `e(D'/D)`. -/
theorem primaryFibres_valuation_dvd
    {E' E B' B : Scheme.{u}}
    (q' : E' ⟶ B') (πE : E' ⟶ E) (πB : B' ⟶ B) (q : E ⟶ B)
    [IsDominant q'] [QuasiCompact q'] [IsDominant πE] [QuasiCompact πE]
    [IsIntegral E'] [IsIntegral E] [IsIntegral B']
    [IsLocallyNoetherian E'] [IsLocallyNoetherian E] [IsLocallyNoetherian B']
    [IsNormalScheme E'] [IsNormalScheme E] [IsNormalScheme B']
    (hcomm : q' ≫ πB = πE ≫ q)
    (F' : SchemeDivisorPoint E')
    (hD' : Order.coheight (q' F'.1) = 1)
    (hF : Order.coheight (πE F'.1) = 1)
    (hred : letI := (q'.stalkMap F'.1).hom.toAlgebra
      _root_.IsReduced (E'.presheaf.stalk F'.1 ⧸
        (maximalIdeal (B'.presheaf.stalk (q' F'.1))).map
          (algebraMap (B'.presheaf.stalk (q' F'.1)) (E'.presheaf.stalk F'.1)))) :
    schemeDivisorRamificationIdx q ⟨πE F'.1, hF⟩ ∣
      schemeDivisorRamificationIdx πB ⟨q' F'.1, hD'⟩ := by
  obtain ⟨h1, h2⟩ := primaryFibres_valuation_display q' πE πB q hcomm F' hD' hF hred
  exact ⟨schemeDivisorRamificationIdx πE F', by rw [← h2, ← h1, mul_comm]⟩

end

#print axioms schemeDivisorRamificationIdx_eq_one_of_reduced_localFibre
#print axioms primaryFibres_valuation_display
#print axioms primaryFibres_valuation_dvd

end Pcf.Bounding
