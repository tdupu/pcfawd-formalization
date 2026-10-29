/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingDictionary

/-!
# Divisorial ramification indices through open-immersion squares

The actual stalk ramification index of a morphism at an integral effective
divisor can be computed on open charts: open immersions have index one, and
indices multiply under composition when the intermediate image is a divisor of
a normal scheme.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf.PaperCharZero

set_option linter.style.haveILetI false

/-- Stalk ramification indices multiply when the intermediate image is a
divisor of a normal scheme; the first morphism need not be finite. -/
theorem schemeDivisorRamificationIdx_comp_of_coheight
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

/-- An open immersion has ramification index one at every divisor. -/
theorem schemeDivisorRamificationIdx_openImmersion
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (x : SchemeDivisorPoint U) :
    schemeDivisorRamificationIdx j x = 1 := by
  apply schemeDivisorRamificationIdx_eq_one_of_formallyEtale
  apply (formallyEtale_stalkMap_iff_etale_neighborhood j x.1).mpr
  exact ⟨⊤, trivial, inferInstance⟩

/-- A nonempty open immersion into an irreducible scheme is dominant. -/
theorem isDominant_of_isOpenImmersion
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [IrreducibleSpace X] [Nonempty U] :
    IsDominant j := by
  constructor
  obtain ⟨u⟩ := (inferInstance : Nonempty U)
  exact j.isOpenEmbedding.isOpen_range.dense ⟨j u, u, rfl⟩

/-- In a commuting square whose vertical maps are open immersions, the index of
the bottom morphism at the image of a divisor equals the index of the top
morphism there. -/
theorem schemeDivisorRamificationIdx_eq_of_openSquare
    {U V X Y : Scheme.{u}} (j : U ⟶ X) (i : V ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion i]
    (g : U ⟶ V) (f : X ⟶ Y) (h : j ≫ f = g ≫ i)
    [IsDominant j] [QuasiCompact j] [IsDominant g] [QuasiCompact g]
    [IsIntegral U] [IsIntegral V] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormalScheme X] [IsLocallyNoetherian V] [IsNormalScheme V]
    (x : SchemeDivisorPoint U) (hjx : Order.coheight (j x.1) = 1)
    (hgx : Order.coheight (g x.1) = 1) :
    schemeDivisorRamificationIdx f ⟨j x.1, hjx⟩ = schemeDivisorRamificationIdx g x := by
  have h1 := schemeDivisorRamificationIdx_comp_of_coheight j f x hjx
  have h2 := schemeDivisorRamificationIdx_comp_of_coheight g i x hgx
  rw [schemeDivisorRamificationIdx_openImmersion j x, mul_one] at h1
  rw [schemeDivisorRamificationIdx_openImmersion i ⟨g x.1, hgx⟩, one_mul] at h2
  rw [← h1, ← h2, h]

#print axioms schemeDivisorRamificationIdx_comp_of_coheight
#print axioms schemeDivisorRamificationIdx_openImmersion
#print axioms isDominant_of_isOpenImmersion
#print axioms schemeDivisorRamificationIdx_eq_of_openSquare

end Pcf.PaperCharZero
