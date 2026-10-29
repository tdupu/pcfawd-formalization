/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.FrobeniusPinchingGalois
public import Pcf.Examples.PaperP.FrobeniusPinchingPCF
public import Pcf.Bounding.PaperPMonodromyDefinition
public import Pcf.Bounding.PrimeToPMonodromyOpenSquare

/-!
# `ex:frobenius-pinching`: the actual function-field extension and its monodromy

`paper-p.tex`, Example `ex:frobenius-pinching`: "Its function-field extension has Galois
group `(ℤ/2ℤ)²`, … so `f` is PCF with monodromy not divisible by `p`."

The generic stalk extension of `H = Spec(x ↦ x², y ↦ y²)` on `A²` is identified, through
Mathlib's `Spec.stalkIso` and `Scheme.localRingHom_comp_stalkIso`, with a pair of fraction
fields of `k[x,y]` related by squaring; `FrobeniusPinchingGalois` then gives a Galois
extension of degree `4` with group `(ℤˣ)² ≅ (ℤ/2ℤ)²`. The prime-to-`p` monodromy moves from
`H` to the canonical lift on the normalization (an isomorphic square) and from the lift down
to `f` itself (the normalization map is birational, so its generic stalk maps are bijective).
-/

@[expose] public section

namespace Pcf.Examples.PaperP.FrobeniusPinchingMonodromy

open AlgebraicGeometry CategoryTheory
open Pcf.Examples.PaperP.FrobeniusPinchingGenerators
open Pcf.Examples.PaperP.FrobeniusPinchingNormalization
open Pcf.Examples.PaperP.FrobeniusPinchingPCF
open Pcf.Examples.PaperP.FrobeniusPinchingGalois

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

/-! ### General transport lemmas -/

/-- A localization at a prime equal to `⊥` is a fraction ring. -/
theorem isFractionRing_atPrime_of_eq_bot {R : Type*} [CommRing R] [IsDomain R]
    (I : Ideal R) [I.IsPrime] (hI : I = ⊥) : IsFractionRing R (Localization.AtPrime I) := by
  have h : I.primeCompl = nonZeroDivisors R := by
    subst hI
    ext r
    simp [Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
  unfold IsFractionRing
  rw [← h]
  infer_instance

/-- **Monodromy across a square, downwards.** If `F ≫ β = α ≫ g` with `α, β` bijective on
the relevant generic stalks, prime-to-`p` monodromy of `F` gives that of `g`. -/
theorem isPrimeToPMonodromyMap_of_square_rev (p : ℕ) {X' Y X₀ Y₀ : Scheme.{u}}
    [IsIntegral X'] [IsIntegral Y] [IsIntegral X₀] [IsIntegral Y₀]
    (F : X' ⟶ Y) (α : X' ⟶ X₀) (β : Y ⟶ Y₀) (g : X₀ ⟶ Y₀)
    [IsFinite F] [IsDominant F] [IsFinite g] [IsDominant g] [IsDominant α]
    (h : F ≫ β = α ≫ g)
    (hα : Function.Bijective (α.stalkMap (genericPoint X')).hom)
    (hβ : Function.Bijective (β.stalkMap (F (genericPoint X'))).hom)
    (hmono : Pcf.IsPrimeToPMonodromyMap p F) : Pcf.IsPrimeToPMonodromyMap p g := by
  obtain ⟨eE, eK, hcomm⟩ := Pcf.exists_stalkEquivs_of_square F α β g h (genericPoint X')
    (map_genericPoint_eq_of_isDominant α) hα hβ
  refine Pcf.isPrimeToPMonodromyMap_of_genericStalkEquivs p F g eK.symm eE.symm ?_ hmono
  apply RingHom.ext
  intro y
  have := congrArg (fun φ => φ (eK.symm y)) hcomm
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.apply_symm_apply] at this
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [this, RingEquiv.symm_apply_apply]

/-! ### The generic stalk extension of `H` -/

variable (k : Type u) [Field k]

/-- The generic point of `A²`, and its image under `H`, are the zero prime. -/
theorem genericPoint_asIdeal :
    (genericPoint (Spec (.of (Plane k)))).asIdeal = ⊥ := by
  rw [genericPoint_eq_bot_of_affine]
  rfl

theorem Hs_genericPoint_asIdeal :
    (Hs k (genericPoint (Spec (.of (Plane k))))).asIdeal = ⊥ := by
  change ((genericPoint (Spec (.of (Plane k)))).asIdeal).comap (square k).toRingHom = ⊥
  rw [genericPoint_asIdeal]
  ext a
  simp only [Ideal.mem_comap, Ideal.mem_bot]
  constructor
  · intro ha
    apply square_injective k
    simpa using ha
  · rintro rfl
    simp

/-- The coordinate map into a stalk of `A²` through `Spec.stalkIso`. -/
noncomputable def stalkCoord (q : Spec (.of (Plane k))) :
    Plane k →+* (Spec (.of (Plane k))).presheaf.stalk q :=
  (Spec.stalkIso (.of (Plane k)) q).inv.hom.comp
    (algebraMap (Plane k) (Localization.AtPrime q.asIdeal))

theorem stalkCoord_isFractionRing (q : Spec (.of (Plane k))) (hq : q.asIdeal = ⊥) :
    @IsFractionRing (Plane k) _ ((Spec (.of (Plane k))).presheaf.stalk q) _
      (stalkCoord k q).toAlgebra := by
  haveI := isFractionRing_atPrime_of_eq_bot q.asIdeal hq
  letI : Algebra (Plane k) ((Spec (.of (Plane k))).presheaf.stalk q) := (stalkCoord k q).toAlgebra
  let e : Localization.AtPrime q.asIdeal ≃ₐ[Plane k] (Spec (.of (Plane k))).presheaf.stalk q :=
    { (Spec.stalkIso (.of (Plane k)) q).symm.commRingCatIsoToRingEquiv with
      commutes' := fun _ => rfl }
  exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors (Plane k)) e

/-- The stalk map of `H` restricts to `square` on coordinates. -/
theorem Hs_stalkMap_stalkCoord (q : Spec (.of (Plane k))) (a : Plane k) :
    (Hs k).stalkMap q (stalkCoord k (Hs k q) a) = stalkCoord k q (square k a) := by
  unfold Hs
  rw [← Scheme.localRingHom_comp_stalkIso]
  simp only [stalkCoord, RingHom.comp_apply, CommRingCat.comp_apply]
  erw [Iso.inv_hom_id_apply]
  rw [ConcreteCategory.comp_apply]
  congr 1
  exact Localization.localRingHom_to_map _ _ _ rfl a

/-- **`H` has prime-to-`p` monodromy**: its actual generic stalk extension is Galois of
degree `4`. -/
theorem Hs_isPrimeToPMonodromyMap (h2 : (2 : k) ≠ 0) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    haveI := Hs_finite k p
    haveI : IsDominant (Hs k) := by haveI := Hs_surjective k p; infer_instance
    Pcf.IsPrimeToPMonodromyMap p (Hs k) := by
  haveI := Hs_finite k p
  haveI : IsDominant (Hs k) := by haveI := Hs_surjective k p; infer_instance
  let X := Spec (.of (Plane k))
  let f := Hs k
  have hgp : f (genericPoint X) = genericPoint X := map_genericPoint_eq_of_isDominant f
  let e := (X.presheaf.stalkCongr (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  letI : Field (X.presheaf.stalk (f (genericPoint X))) :=
    (e.toMulEquiv.isField (Field.toIsField _)).toField
  letI : Algebra (X.presheaf.stalk (f (genericPoint X))) (X.presheaf.stalk (genericPoint X)) :=
    (f.stalkMap (genericPoint X)).hom.toAlgebra
  change Pcf.IsPrimeToPMonodromy.{u, u, u} p
    (X.presheaf.stalk (f (genericPoint X))) (X.presheaf.stalk (genericPoint X))
  refine isPrimeToPMonodromy_of_squareFractionData (i := stalkCoord k (f (genericPoint X)))
    (j := stalkCoord k (genericPoint X)) p Fact.out hp2 h2 ⟨?_, ?_, ?_⟩
  · exact stalkCoord_isFractionRing k _ (Hs_genericPoint_asIdeal k)
  · exact stalkCoord_isFractionRing k _ (genericPoint_asIdeal k)
  · apply RingHom.ext
    intro a
    exact Hs_stalkMap_stalkCoord k (genericPoint X) a

/-- The target generic stalk of `H` is a field. -/
theorem Hs_generic_isField :
    IsField ((Spec (.of (Plane k))).presheaf.stalk
      (Hs k (genericPoint (Spec (.of (Plane k)))))) := by
  haveI := isFractionRing_atPrime_of_eq_bot _ (Hs_genericPoint_asIdeal k)
  letI : Field (Localization.AtPrime (Hs k (genericPoint (Spec (.of (Plane k))))).asIdeal) :=
    IsFractionRing.toField (Plane k)
  exact (Spec.stalkIso (.of (Plane k)) _).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField _)

/-- **The actual function-field extension of `H` is Galois of degree `4` with group
`(ℤˣ)² ≅ (ℤ/2ℤ)²`**, the extension being the generic stalk map of `H` (any field structure on
the target stalk; it is unique as a proposition `IsField`). -/
theorem Hs_generic_galois (h2 : (2 : k) ≠ 0)
    (hF : IsField ((Spec (.of (Plane k))).presheaf.stalk
      (Hs k (genericPoint (Spec (.of (Plane k))))))) :
    letI := hF.toField
    letI := ((Hs k).stalkMap (genericPoint (Spec (.of (Plane k))))).hom.toAlgebra
    IsGalois ((Spec (.of (Plane k))).presheaf.stalk (Hs k (genericPoint (Spec (.of (Plane k))))))
        ((Spec (.of (Plane k))).presheaf.stalk (genericPoint (Spec (.of (Plane k))))) ∧
      Module.finrank
        ((Spec (.of (Plane k))).presheaf.stalk (Hs k (genericPoint (Spec (.of (Plane k))))))
        ((Spec (.of (Plane k))).presheaf.stalk (genericPoint (Spec (.of (Plane k))))) = 4 ∧
      Nonempty ((((Spec (.of (Plane k))).presheaf.stalk (genericPoint (Spec (.of (Plane k))))) ≃ₐ[
        (Spec (.of (Plane k))).presheaf.stalk (Hs k (genericPoint (Spec (.of (Plane k)))))]
        ((Spec (.of (Plane k))).presheaf.stalk (genericPoint (Spec (.of (Plane k)))))) ≃*
          SignGroup) := by
  letI := hF.toField
  letI := ((Hs k).stalkMap (genericPoint (Spec (.of (Plane k))))).hom.toAlgebra
  exact galois_of_squareFractionData
    (i := stalkCoord k (Hs k (genericPoint (Spec (.of (Plane k))))))
    (j := stalkCoord k (genericPoint (Spec (.of (Plane k))))) h2
    ⟨stalkCoord_isFractionRing k _ (Hs_genericPoint_asIdeal k),
      stalkCoord_isFractionRing k _ (genericPoint_asIdeal k),
      RingHom.ext fun a => Hs_stalkMap_stalkCoord k (genericPoint (Spec (.of (Plane k)))) a⟩

/-! ### Down to `f` -/

variable (p : ℕ) [Fact p.Prime]

instance liftFinite : IsFinite (lift k p) := lift_finite k p

instance liftDominant : IsDominant (lift k p) := lift_dominant k p

theorem iso_stalk_bijective {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (x : X) :
    Function.Bijective (e.stalkMap x).hom :=
  (asIso (e.stalkMap x)).commRingCatIsoToRingEquiv.bijective

/-- The canonical lift `normIso⁻¹ ∘ H ∘ normIso` has prime-to-`p` monodromy. -/
theorem lift_isPrimeToPMonodromyMap (h2 : (2 : k) ≠ 0) (hp2 : p ≠ 2) :
    Pcf.IsPrimeToPMonodromyMap p (lift k p) := by
  haveI := Hs_finite k p
  haveI : IsDominant (Hs k) := by haveI := Hs_surjective k p; infer_instance
  have hsq : lift k p ≫ (normIso k p).hom = (normIso k p).hom ≫ Hs k := by
    simp [lift]
  exact Pcf.isPrimeToPMonodromyMap_of_openImmersion_square p (lift k p) (normIso k p).hom
    (normIso k p).hom (Hs k) hsq (Hs_isPrimeToPMonodromyMap k h2 p hp2)

/-- **`f` has prime-to-`p` monodromy** (the source's "monodromy not divisible by `p`"). -/
theorem f_isPrimeToPMonodromyMap (h2 : (2 : k) ≠ 0) (hp2 : p ≠ 2) :
    Pcf.IsPrimeToPMonodromyMap p (descendedSchemeMap k p) := by
  let N := Pcf.Palomar.normalization (Xs k p)
  let n := Pcf.Palomar.normalizationMap (Xs k p)
  have hgen : lift k p (genericPoint N) = genericPoint N :=
    map_genericPoint_eq_of_isDominant (lift k p)
  have hiso : IsIso (n.stalkMap (genericPoint N)) := by
    change IsIso ((Pcf.Palomar.normalizationMap (Xs k p)).stalkMap
      (genericPoint (Pcf.Palomar.normalization (Xs k p))))
    infer_instance
  have hα : Function.Bijective (n.stalkMap (genericPoint N)).hom :=
    (asIso (n.stalkMap (genericPoint N))).commRingCatIsoToRingEquiv.bijective
  have hβ : Function.Bijective (n.stalkMap (lift k p (genericPoint N))).hom := by
    rw [hgen]
    exact hα
  exact isPrimeToPMonodromyMap_of_square_rev p (lift k p) n n (descendedSchemeMap k p)
    (lift_comp_normalizationMap k p) hα hβ (lift_isPrimeToPMonodromyMap k p h2 hp2)

/-- The manuscript's monodromy predicate for `f`, in characteristic `p ≥ 5`.

`paper-p.tex` correspondence: Example 4.5 (`ex:frobenius-pinching`). -/
theorem f_isPaperPMonodromyNotDivisibleBy [CharP k p] (hp : 5 ≤ p) :
    Pcf.IsPaperPMonodromyNotDivisibleBy p (descendedSchemeMap k p) :=
  (Pcf.isPaperPMonodromyNotDivisibleBy_iff_of_prime p _).mpr
    (f_isPrimeToPMonodromyMap k p (two_ne_zero_of_charP k p (by omega)) (by omega))

/-- **`ex:frobenius-pinching`, complete source statement**: for `char k = p ≥ 5`, the
descended map `f` on the pinched surface is PCF (separable normalized weighted PCF) with
monodromy not divisible by `p`.

`paper-p.tex` correspondence: Example 4.5 (`ex:frobenius-pinching`). -/
theorem f_isPCF_with_monodromy_not_divisible [CharP k p] (hp : 5 ≤ p) :
    Pcf.IsSeparableNormalizedPCF k (structureMap k p) (descendedSchemeMap k p) ∧
      Pcf.IsPaperPMonodromyNotDivisibleBy p (descendedSchemeMap k p) :=
  ⟨f_isSeparableNormalizedPCF_of_charP k p hp, f_isPaperPMonodromyNotDivisibleBy k p hp⟩

#print axioms isPrimeToPMonodromyMap_of_square_rev
#print axioms Hs_isPrimeToPMonodromyMap
#print axioms Hs_generic_galois
#print axioms lift_isPrimeToPMonodromyMap
#print axioms f_isPrimeToPMonodromyMap
#print axioms f_isPaperPMonodromyNotDivisibleBy
#print axioms f_isPCF_with_monodromy_not_divisible

end Pcf.Examples.PaperP.FrobeniusPinchingMonodromy
