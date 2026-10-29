/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeDynamics
public import Pcf.Bounding.PrimaryFibresScheme
public import Pcf.Bounding.PrimaryFibresCharZeroScheme
public import Pcf.Bounding.AllCodimBadFiniteTopology
public import Pcf.Ramification

/-!
# Ramification indices in the blow-up comparison square

The proof of `paper-p.tex`, Proposition `prop:bound-blowup`, compares orders
of a local equation around a square involving exceptional components. The
identities here use ramification indices of the *actual scheme stalk maps*.
They apply after the paper's normalizations and divisor lifts have been
constructed; no finiteness of the vertical component map is required.
-/

@[expose] public section

namespace Pcf.Bounding

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

/-- Stalk ramification indices multiply when the intermediate image is a
divisor, even if the first morphism is proper rather than finite. -/
theorem schemeDivisorRamificationIdx_comp_of_divisorImage
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsDominant f] [QuasiCompact f]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormalScheme Y]
    (x : SchemeDivisorPoint X) (hy : Order.coheight (f x.1) = 1) :
    schemeDivisorRamificationIdx (f ≫ g) x =
      schemeDivisorRamificationIdx g ⟨f x.1, hy⟩ *
        schemeDivisorRamificationIdx f x := by
  let R := Z.presheaf.stalk (g (f x.1))
  let S := Y.presheaf.stalk (f x.1)
  let T := X.presheaf.stalk x.1
  letI : Algebra R S := (g.stalkMap (f x.1)).hom.toAlgebra
  letI : Algebra S T := (f.stalkMap x.1).hom.toAlgebra
  letI : Algebra R T := ((f ≫ g).stalkMap x.1).hom.toAlgebra
  letI : IsLocalHom (algebraMap S T) :=
    show IsLocalHom (f.stalkMap x.1).hom from inferInstance
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' (by
    change ((f ≫ g).stalkMap x.1).hom =
      (f.stalkMap x.1).hom.comp (g.stalkMap (f x.1)).hom
    rw [Scheme.Hom.stalkMap_comp]
    rfl)
  let y : SchemeDivisorPoint Y := ⟨f x.1, hy⟩
  letI : IsDiscreteValuationRing S := y.stalk_isDiscreteValuationRing
  letI : FaithfulSMul S T := (faithfulSMul_iff_algebraMap_injective S T).mpr
    (stalkMap_injective_of_dominant_integral f x.1)
  letI : Module.Flat S T := inferInstance
  exact Ideal.ramificationIdx_tower (R := R) (IsLocalRing.maximalIdeal S)
    (IsLocalRing.maximalIdeal T)

/-- The two paths through an actual commutative square of normal schemes
have the same valuation multiplicity at a divisor. In `prop:bound-blowup`,
`u` is the lifted restriction, `v` the proper map to the original
restriction, `q` the exceptional-component map, and `g` the restricted map. -/
theorem schemeDivisorRamificationIdx_square
    {X Y W Z : Scheme.{u}}
    (u : X ⟶ Y) (v : X ⟶ W) (q : Y ⟶ Z) (g : W ⟶ Z)
    [IsDominant u] [QuasiCompact u] [IsDominant v] [QuasiCompact v]
    [IsIntegral X] [IsIntegral Y] [IsIntegral W]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian W]
    [IsNormalScheme Y] [IsNormalScheme W]
    (hcomm : u ≫ q = v ≫ g)
    (x : SchemeDivisorPoint X)
    (hy : Order.coheight (u x.1) = 1)
    (hw : Order.coheight (v x.1) = 1) :
    schemeDivisorRamificationIdx q ⟨u x.1, hy⟩ *
        schemeDivisorRamificationIdx u x =
      schemeDivisorRamificationIdx g ⟨v x.1, hw⟩ *
        schemeDivisorRamificationIdx v x := by
  calc
    _ = schemeDivisorRamificationIdx (u ≫ q) x :=
      (schemeDivisorRamificationIdx_comp_of_divisorImage u q x hy).symm
    _ = schemeDivisorRamificationIdx (v ≫ g) x := by rw [hcomm]
    _ = _ := schemeDivisorRamificationIdx_comp_of_divisorImage v g x hw

/-- In the actual scheme square, étaleness of the lifted restriction and
the primary-fibre multiplicity of the exceptional-component map force the
original restricted map to have index one when its index is prime to `p`.
The primary-fibre premise is supplied by `PrimaryFibresScheme` outside a
fixed proper closed set. -/
theorem schemeDivisorRamificationIdx_eq_one_of_primary_square
    {X Y W Z : Scheme.{u}}
    (u : X ⟶ Y) (v : X ⟶ W) (q : Y ⟶ Z) (g : W ⟶ Z)
    [IsDominant u] [QuasiCompact u] [LocallyOfFiniteType u]
    [IsDominant v] [QuasiCompact v]
    [IsIntegral X] [IsIntegral Y] [IsIntegral W]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian W]
    [IsNormalScheme Y] [IsNormalScheme W]
    (hcomm : u ≫ q = v ≫ g)
    (x : SchemeDivisorPoint X)
    (hy : Order.coheight (u x.1) = 1)
    (hw : Order.coheight (v x.1) = 1)
    (p b : ℕ) (hp : p.Prime)
    (hprimary : schemeDivisorRamificationIdx q ⟨u x.1, hy⟩ = p ^ b)
    (hetale : (u.stalkMap x.1).hom.FormallyEtale)
    (htame : (schemeDivisorRamificationIdx g ⟨v x.1, hw⟩).Coprime p) :
    schemeDivisorRamificationIdx g ⟨v x.1, hw⟩ = 1 := by
  have hsq := schemeDivisorRamificationIdx_square u v q g hcomm x hy hw
  have hu := schemeDivisorRamificationIdx_eq_one_of_formallyEtale u x hetale
  rw [hu, mul_one, hprimary] at hsq
  have hdiv : schemeDivisorRamificationIdx g ⟨v x.1, hw⟩ ∣ p ^ b :=
    ⟨schemeDivisorRamificationIdx v x, hsq⟩
  exact Pcf.Ramification.index_eq_one_of_dvd_prime_pow hp
    (hp.coprime_iff_not_dvd.mp htame.symm) hdiv

/-- For a *fixed actual* exceptional-component map `q`, the primary-fibre
theorem gives one dense open on the base where every compatible square
with an étale upper map and tame lower map has lower index one. The
existence of the normalized component maps and their divisor lifts is a
separate geometric step in `prop:bound-blowup`. -/
theorem exists_open_eq_one_of_primary_blowup_square
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    {X Y W Z : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral W] [IsIntegral Z]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian W] [IsLocallyNoetherian Z]
    [IsNormalScheme Y] [IsNormalScheme W] [IsNormalScheme Z]
    [CompactSpace Z]
    (s : Z ⟶ Spec (.of k))
    (u : X ⟶ Y) (v : X ⟶ W) (q : Y ⟶ Z) (g : W ⟶ Z)
    [IsDominant u] [QuasiCompact u] [LocallyOfFiniteType u]
    [IsDominant v] [QuasiCompact v]
    [IsDominant q] [LocallyOfFiniteType q] [QuasiCompact q]
    (hcomm : u ≫ q = v ≫ g) :
    ∃ U : Z.Opens, (U : Set Z).Nonempty ∧
      ∀ (x : SchemeDivisorPoint X)
        (_hy : Order.coheight (u x.1) = 1)
        (hw : Order.coheight (v x.1) = 1)
        (_hz : Order.coheight (q (u x.1)) = 1),
        q (u x.1) ∈ U →
        (u.stalkMap x.1).hom.FormallyEtale →
        (schemeDivisorRamificationIdx g ⟨v x.1, hw⟩).Coprime p →
        schemeDivisorRamificationIdx g ⟨v x.1, hw⟩ = 1 := by
  obtain ⟨U, hU, a, hprimary⟩ :=
    exists_open_schemeDivisorRamificationIdx_eq_prime_pow p k s q
  refine ⟨U, hU, ?_⟩
  intro x hy hw hz hxU hetale htame
  obtain ⟨b, _hb, hpow⟩ := hprimary
    (⟨u x.1, hy⟩ : SchemeDivisorPoint Y)
    (⟨q (u x.1), hz⟩ : SchemeDivisorPoint Z) rfl hxU
  exact schemeDivisorRamificationIdx_eq_one_of_primary_square
    u v q g hcomm x hy hw p b (Fact.out) hpow hetale htame

/-- The bad codimension-one points for a fixed actual component map `q`
form a finite set, uniformly for every compatible upper map `u` and
vertical map `v` satisfying the square. This isolates the finite-set
portion of `prop:bound-blowup`; the exceptional-component and divisor-lift
construction remains to be connected to it. -/
theorem exists_finite_bad_of_primary_blowup_square
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    {X Y W Z : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral W] [IsIntegral Z]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian W] [IsLocallyNoetherian Z]
    [IsNormalScheme Y] [IsNormalScheme W] [IsNormalScheme Z]
    [CompactSpace Z] [NoetherianSpace Z]
    (s : Z ⟶ Spec (.of k))
    (u : X ⟶ Y) (v : X ⟶ W) (q : Y ⟶ Z) (g : W ⟶ Z)
    [IsDominant u] [QuasiCompact u] [LocallyOfFiniteType u]
    [IsDominant v] [QuasiCompact v]
    [IsDominant q] [LocallyOfFiniteType q] [QuasiCompact q]
    (hcomm : u ≫ q = v ≫ g) :
    ∃ Bad : Set Z, Bad.Finite ∧
      ∀ (x : SchemeDivisorPoint X)
        (_hy : Order.coheight (u x.1) = 1)
        (hw : Order.coheight (v x.1) = 1)
        (_hz : Order.coheight (q (u x.1)) = 1),
        q (u x.1) ∉ Bad →
        (u.stalkMap x.1).hom.FormallyEtale →
        (schemeDivisorRamificationIdx g ⟨v x.1, hw⟩).Coprime p →
        schemeDivisorRamificationIdx g ⟨v x.1, hw⟩ = 1 := by
  obtain ⟨U, hU, hindex⟩ :=
    exists_open_eq_one_of_primary_blowup_square p k s u v q g hcomm
  let Bad : Set Z := {z | z ∉ U ∧ Order.coheight z = 1}
  have hη : genericPoint Z ∈ U :=
    ((genericPoint_spec Z).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have hBadFinite : Bad.Finite :=
    finite_coheight_one_of_isClosed (U : Set Z)ᶜ U.isOpen.isClosed_compl
      (by simpa using hη)
  refine ⟨Bad, hBadFinite, ?_⟩
  intro x hy hw hz hnotBad hetale htame
  have hxU : q (u x.1) ∈ U := by
    by_contra h
    exact hnotBad ⟨h, hz⟩
  exact hindex x hy hw hz hxU hetale htame

/-- The finite bad set is selected from the fixed component map `q` alone.
It works for *all* compatible normalized restriction squares, as needed
when the maps upstairs vary with the tower level. -/
theorem exists_finite_bad_for_component_map
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    {Y Z : Scheme.{u}}
    [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    [IsNormalScheme Y] [IsNormalScheme Z]
    [CompactSpace Z] [NoetherianSpace Z]
    (s : Z ⟶ Spec (.of k)) (q : Y ⟶ Z)
    [IsDominant q] [LocallyOfFiniteType q] [QuasiCompact q] :
    ∃ Bad : Set Z, Bad.Finite ∧
      ∀ {X W : Scheme.{u}}
        [IsIntegral X] [IsIntegral W]
        [IsLocallyNoetherian W] [IsNormalScheme W]
        (u : X ⟶ Y) (v : X ⟶ W) (g : W ⟶ Z)
        [IsDominant u] [QuasiCompact u] [LocallyOfFiniteType u]
        [IsDominant v] [QuasiCompact v]
        (_hcomm : u ≫ q = v ≫ g)
        (x : SchemeDivisorPoint X)
        (_hy : Order.coheight (u x.1) = 1)
        (hw : Order.coheight (v x.1) = 1)
        (_hz : Order.coheight (q (u x.1)) = 1),
        q (u x.1) ∉ Bad →
        (u.stalkMap x.1).hom.FormallyEtale →
        (schemeDivisorRamificationIdx g ⟨v x.1, hw⟩).Coprime p →
        schemeDivisorRamificationIdx g ⟨v x.1, hw⟩ = 1 := by
  obtain ⟨U, hU, a, hprimary⟩ :=
    exists_open_schemeDivisorRamificationIdx_eq_prime_pow p k s q
  let Bad : Set Z := {z | z ∉ U ∧ Order.coheight z = 1}
  have hη : genericPoint Z ∈ U :=
    ((genericPoint_spec Z).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have hBadFinite : Bad.Finite :=
    finite_coheight_one_of_isClosed (U : Set Z)ᶜ U.isOpen.isClosed_compl
      (by simpa using hη)
  refine ⟨Bad, hBadFinite, ?_⟩
  intro X W _ _ _ _ u v g _ _ _ _ _ hcomm x hy hw hz hnotBad hetale htame
  have hxU : q (u x.1) ∈ U := by
    by_contra h
    exact hnotBad ⟨h, hz⟩
  obtain ⟨b, _hb, hpow⟩ := hprimary
    (⟨u x.1, hy⟩ : SchemeDivisorPoint Y)
    (⟨q (u x.1), hz⟩ : SchemeDivisorPoint Z) rfl hxU
  exact schemeDivisorRamificationIdx_eq_one_of_primary_square
    u v q g hcomm x hy hw p b (Fact.out) hpow hetale htame

/-- Characteristic-zero version of the valuation-square conclusion: if
the fixed component map has reduced fibre and the upper restriction is
étale, then the lower restriction has index one. -/
theorem schemeDivisorRamificationIdx_eq_one_of_reduced_square
    {X Y W Z : Scheme.{u}}
    (u : X ⟶ Y) (v : X ⟶ W) (q : Y ⟶ Z) (g : W ⟶ Z)
    [IsDominant u] [QuasiCompact u] [LocallyOfFiniteType u]
    [IsDominant v] [QuasiCompact v]
    [IsIntegral X] [IsIntegral Y] [IsIntegral W]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian W]
    [IsNormalScheme Y] [IsNormalScheme W]
    (hcomm : u ≫ q = v ≫ g)
    (x : SchemeDivisorPoint X)
    (hy : Order.coheight (u x.1) = 1)
    (hw : Order.coheight (v x.1) = 1)
    (hreduced : schemeDivisorRamificationIdx q ⟨u x.1, hy⟩ = 1)
    (hetale : (u.stalkMap x.1).hom.FormallyEtale) :
    schemeDivisorRamificationIdx g ⟨v x.1, hw⟩ = 1 := by
  have hsq := schemeDivisorRamificationIdx_square u v q g hcomm x hy hw
  have hu := schemeDivisorRamificationIdx_eq_one_of_formallyEtale u x hetale
  rw [hu, hreduced, mul_one] at hsq
  exact Nat.dvd_one.mp ⟨schemeDivisorRamificationIdx v x, hsq⟩

/-- In characteristic zero, the fixed component map `q` has a finite
set of bad divisors, independent of all varying compatible squares. -/
theorem exists_finite_bad_for_component_map_charZero
    (k : Type u) [Field k] [CharZero k]
    {Y Z : Scheme.{u}}
    [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    [IsNormalScheme Y] [IsNormalScheme Z]
    [CompactSpace Z] [NoetherianSpace Z]
    (s : Z ⟶ Spec (.of k)) (q : Y ⟶ Z)
    [IsDominant q] [LocallyOfFiniteType q] [QuasiCompact q] :
    ∃ Bad : Set Z, Bad.Finite ∧
      ∀ {X W : Scheme.{u}}
        [IsIntegral X] [IsIntegral W]
        [IsLocallyNoetherian W] [IsNormalScheme W]
        (u : X ⟶ Y) (v : X ⟶ W) (g : W ⟶ Z)
        [IsDominant u] [QuasiCompact u] [LocallyOfFiniteType u]
        [IsDominant v] [QuasiCompact v]
        (_hcomm : u ≫ q = v ≫ g)
        (x : SchemeDivisorPoint X)
        (_hy : Order.coheight (u x.1) = 1)
        (hw : Order.coheight (v x.1) = 1)
        (_hz : Order.coheight (q (u x.1)) = 1),
        q (u x.1) ∉ Bad →
        (u.stalkMap x.1).hom.FormallyEtale →
        schemeDivisorRamificationIdx g ⟨v x.1, hw⟩ = 1 := by
  obtain ⟨U, hU, hprimary⟩ :=
    exists_open_schemeDivisorRamificationIdx_eq_one_charZero k s q
  let Bad : Set Z := {z | z ∉ U ∧ Order.coheight z = 1}
  have hη : genericPoint Z ∈ U :=
    ((genericPoint_spec Z).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have hBadFinite : Bad.Finite :=
    finite_coheight_one_of_isClosed (U : Set Z)ᶜ U.isOpen.isClosed_compl
      (by simpa using hη)
  refine ⟨Bad, hBadFinite, ?_⟩
  intro X W _ _ _ _ u v g _ _ _ _ _ hcomm x hy hw hz hnotBad hetale
  have hxU : q (u x.1) ∈ U := by
    by_contra h
    exact hnotBad ⟨h, hz⟩
  have hq : schemeDivisorRamificationIdx q ⟨u x.1, hy⟩ = 1 :=
    hprimary (⟨u x.1, hy⟩ : SchemeDivisorPoint Y)
      (⟨q (u x.1), hz⟩ : SchemeDivisorPoint Z) rfl hxU
  exact schemeDivisorRamificationIdx_eq_one_of_reduced_square
    u v q g hcomm x hy hw hq hetale

#print axioms schemeDivisorRamificationIdx_comp_of_divisorImage
#print axioms schemeDivisorRamificationIdx_square
#print axioms schemeDivisorRamificationIdx_eq_one_of_primary_square
#print axioms exists_open_eq_one_of_primary_blowup_square
#print axioms exists_finite_bad_of_primary_blowup_square
#print axioms exists_finite_bad_for_component_map
#print axioms schemeDivisorRamificationIdx_eq_one_of_reduced_square
#print axioms exists_finite_bad_for_component_map_charZero

end
end Pcf.Bounding
