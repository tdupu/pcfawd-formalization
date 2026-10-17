/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeBridge
public import Mathlib.Topology.KrullDimension

/-!
# Finiteness of the actual codimension-one critical locus

The critical predicate is the failure of formal étaleness of the actual stalk map,
as in `schemeDivisorNonEtaleLocus`. A proper closed locus in an irreducible scheme contains
only finitely many divisor points when that locus is Noetherian. This supplies the
topological finiteness step without assuming finiteness of the divisor locus itself.

For locally finitely presented morphisms, affine stalk coordinates identify this
predicate with the complement of the affine étale locus, proving closedness.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

/-- The full point locus where the actual stalk map is not formally étale. -/
def schemeNonEtaleLocus {X Y : Scheme.{u}} (g : X ⟶ Y) : Set X :=
  {x | SchemeStalkNotFormallyEtaleAt g x}

/-- The actual stalk criterion agrees with the affine étale locus. -/
theorem formallyEtale_stalkMap_iff
    {X Y : Scheme.{u}} {f : X ⟶ Y} {x : X}
    (U : Y.Opens) (hU : IsAffineOpen U)
    (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    (f.stalkMap x).hom.FormallyEtale ↔
      hV.primeIdealOf ⟨x, hx⟩ ∈ Algebra.etaleLocus Γ(Y, U) Γ(X, V) := by
  let := (f.appLE U V hVU).hom.toAlgebra
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  trans Algebra.FormallyEtale (Localization.AtPrime p) (Localization.AtPrime q)
  · rw [← RingHom.formallyEtale_algebraMap]
    exact formallyEtale_respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx)
  · exact Algebra.FormallyEtale.iff_restrictScalars.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A formally étale stalk of a locally finitely presented morphism has affine
neighborhoods on which the section-ring map is étale. -/
theorem exists_etale_of_formallyEtale_stalk
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (x : X) (H : (f.stalkMap x).hom.FormallyEtale) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V)
      (hVU : V ≤ f ⁻¹ᵁ U), x ∈ V ∧ (f.appLE U V hVU).hom.Etale := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.finitePresentation_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  have : Algebra.IsEtaleAt _ _ := (formallyEtale_stalkMap_iff U hU V hV hVU hxV).mp H
  obtain ⟨r, hrx, hr⟩ := Algebra.exists_etale_of_isEtaleAt (R := Γ(Y, U))
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  refine ⟨_, hU, _, hV.basicOpen r, (X.basicOpen_le r).trans hVU, ?_, ?_⟩
  · rwa [← PrimeSpectrum.mem_basicOpen, IsAffineOpen.primeIdealOf,
      ← hV.fromSpec_preimage_basicOpen, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
      IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec] at hrx
  · have := hV.isLocalization_basicOpen r
    rw [← RingHom.etale_algebraMap] at hr
    convert!
      RingHom.Etale.propertyIsLocal.respectsIso.1 _
        (IsLocalization.algEquiv (.powers r) _ Γ(X, X.basicOpen r)).toRingEquiv hr
    ext
    dsimp
    simp only [IsScalarTower.algebraMap_apply Γ(Y, U) Γ(X, V) (Localization _),
      IsLocalization.map_eq]
    simp only [RingHom.algebraMap_toAlgebra, RingHomCompTriple.comp_apply,
      ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]

/-- The actual formally étale stalk locus is open for a locally finitely
presented scheme morphism. -/
theorem isOpen_formallyEtale_stalkLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    IsOpen {x | (f.stalkMap x).hom.FormallyEtale} := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  obtain ⟨U, hU, V, hV, hVU, hxV, H⟩ := exists_etale_of_formallyEtale_stalk f x hx
  algebraize [(f.appLE U V hVU).hom]
  exact ⟨V, fun y hy ↦ (formallyEtale_stalkMap_iff U hU V hV hVU hy).mpr
    (inferInstanceAs (Algebra.IsEtaleAt _ _)), V.2, hxV⟩

/-- A dominant morphism between irreducible schemes sends the generic point to
the generic point. -/
theorem map_genericPoint_eq_of_isDominant
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    [IrreducibleSpace Y] [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  convert! (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range]

/-- On an irreducible scheme, a nonempty open formally étale locus contains the
generic point. -/
theorem formallyEtale_stalkMap_genericPoint_of_exists
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    [LocallyOfFinitePresentation f]
    (h : ∃ x : X, (f.stalkMap x).hom.FormallyEtale) :
    (f.stalkMap (genericPoint X)).hom.FormallyEtale := by
  let U : Set X := {x | (f.stalkMap x).hom.FormallyEtale}
  have hUopen : IsOpen U := isOpen_formallyEtale_stalkLocus f
  have hUne : U.Nonempty := h
  exact ((genericPoint_spec X).mem_open_set_iff hUopen).mpr <| by
    simpa only [Set.univ_inter] using hUne

set_option linter.style.haveILetI false in
/-- In characteristic zero, the generic stalk of a finite dominant endomorphism
of an integral scheme is formally étale. The two generic stalks are fields;
quasi-finiteness makes the induced extension finite, and characteristic zero
makes it separable. -/
theorem formallyEtale_stalkMap_genericPoint_of_finite_dominant_charZero
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f] [IsIntegral X]
    [CharZero (X.presheaf.stalk (genericPoint X))] :
    (f.stalkMap (genericPoint X)).hom.FormallyEtale := by
  have hgp : f (genericPoint X) = genericPoint X :=
    map_genericPoint_eq_of_isDominant f
  let e := (X.presheaf.stalkCongr (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  have hfield : IsField (X.presheaf.stalk (f (genericPoint X))) :=
    e.toMulEquiv.isField (Field.toIsField _)
  letI : Field (X.presheaf.stalk (f (genericPoint X))) :=
    hfield.toField
  letI : CharZero (X.presheaf.stalk (f (genericPoint X))) :=
    charZero_of_injective_ringHom e.symm.injective
  letI := (f.stalkMap (genericPoint X)).hom.toAlgebra
  letI : FaithfulSMul (X.presheaf.stalk (f (genericPoint X)))
      (X.presheaf.stalk (genericPoint X)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (f.stalkMap (genericPoint X)).hom.injective
  letI : Algebra.QuasiFinite (X.presheaf.stalk (f (genericPoint X)))
      (X.presheaf.stalk (genericPoint X)) := f.quasiFiniteAt (genericPoint X)
  letI : Module.Finite (X.presheaf.stalk (f (genericPoint X)))
      (X.presheaf.stalk (genericPoint X)) :=
    Algebra.QuasiFinite.iff_of_isArtinianRing.mp inferInstance
  letI : PerfectField (X.presheaf.stalk (f (genericPoint X))) :=
    PerfectField.ofCharZero
  rw [RingHom.FormallyEtale]
  exact Algebra.FormallyEtale.of_isSeparable
    (X.presheaf.stalk (f (genericPoint X)))
    (X.presheaf.stalk (genericPoint X))

/-- One formally étale stalk of a dominant finite-presentation endomorphism of an
irreducible scheme supplies a formally étale stalk for every iterate. -/
theorem exists_formallyEtale_stalk_iterate_of_exists
    {X : Scheme.{u}} (f : X ⟶ X) [IrreducibleSpace X]
    [IsDominant f] [LocallyOfFinitePresentation f]
    (h : ∃ x : X, (f.stalkMap x).hom.FormallyEtale) :
    ∀ m, ∃ x : X,
      ((CategoryTheory.End.of f ^ m).asHom.stalkMap x).hom.FormallyEtale := by
  have hfg := formallyEtale_stalkMap_genericPoint_of_exists f h
  have hgp : f (genericPoint X) = genericPoint X :=
    map_genericPoint_eq_of_isDominant f
  intro m
  refine ⟨genericPoint X, ?_⟩
  induction m with
  | zero =>
      rw [pow_zero]
      change ((𝟙 X : X ⟶ X).stalkMap (genericPoint X)).hom.FormallyEtale
      rw [Scheme.Hom.stalkMap_id]
      change (RingHom.id _).FormallyEtale
      rw [RingHom.FormallyEtale]
      infer_instance
  | succ m ih =>
      rw [pow_succ, CategoryTheory.End.mul_asHom]
      change ((f ≫ (CategoryTheory.End.of f ^ m).asHom).stalkMap
        (genericPoint X)).hom.FormallyEtale
      rw [Scheme.Hom.stalkMap_comp]
      change ((f.stalkMap (genericPoint X)).hom.comp
        (((CategoryTheory.End.of f ^ m).asHom.stalkMap
          (f (genericPoint X))).hom)).FormallyEtale
      have hi : (((CategoryTheory.End.of f ^ m).asHom.stalkMap
          (f (genericPoint X))).hom).FormallyEtale := by
        rw [hgp]
        exact ih
      exact RingHom.FormallyEtale.comp hi hfg

/-- The full critical locus defined using the actual stalk map is closed. -/
theorem isClosed_schemeNonEtaleLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    IsClosed (schemeNonEtaleLocus f) :=
  (isOpen_formallyEtale_stalkLocus f).isClosed_compl

/-- A proper closed Noetherian subspace of an irreducible scheme contains only
finitely many codimension-one points. No normality or reducedness is required. -/
theorem finite_schemeDivisorPoint_mem_of_isClosed
    {X : Scheme.{u}} [IrreducibleSpace X] {C : Set X}
    [NoetherianSpace C] (hC : IsClosed C) (hproper : C ≠ Set.univ) :
    {x : SchemeDivisorPoint X | x.1 ∈ C}.Finite := by
  let : QuasiSober C := hC.isClosedEmbedding_subtypeVal.quasiSober
  have hfin : {x ∈ C | Order.coheight x = 1}.Finite :=
    NoetherianSpace.finite_coheight_one_of_closure_ne_univ
      (by simpa only [hC.closure_eq] using hproper)
  exact (hfin.preimage Subtype.val_injective.injOn).subset fun x hx => ⟨hx, x.2⟩

/-- The actual codimension-one critical locus is finite if its full point locus is
closed, proper, and Noetherian, and the source is irreducible. -/
theorem schemeDivisorNonEtaleLocus_finite_of_isClosed
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IrreducibleSpace X]
    [NoetherianSpace (schemeNonEtaleLocus g)]
    (hclosed : IsClosed (schemeNonEtaleLocus g))
    (hproper : schemeNonEtaleLocus g ≠ Set.univ) :
    (schemeDivisorNonEtaleLocus g).Finite :=
  finite_schemeDivisorPoint_mem_of_isClosed hclosed hproper

/-- For a closed critical locus on an irreducible source, one formally étale
stalk supplies properness. No dense-open étale locus needs to be supplied. -/
theorem schemeDivisorNonEtaleLocus_finite_of_isClosed_of_exists_formallyEtale
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IrreducibleSpace X]
    [NoetherianSpace (schemeNonEtaleLocus g)]
    (hclosed : IsClosed (schemeNonEtaleLocus g))
    (hetale : ∃ x : X, (g.stalkMap x).hom.FormallyEtale) :
    (schemeDivisorNonEtaleLocus g).Finite := by
  apply schemeDivisorNonEtaleLocus_finite_of_isClosed g hclosed
  intro h
  obtain ⟨x, hx⟩ := hetale
  have hmem : x ∈ schemeNonEtaleLocus g := h.symm ▸ Set.mem_univ x
  exact hmem hx

/-- On an irreducible Noetherian source, a locally finitely presented morphism
with one formally étale stalk has finitely many critical divisor points. -/
theorem schemeDivisorNonEtaleLocus_finite_of_exists_formallyEtale
    {X Y : Scheme.{u}} (g : X ⟶ Y) [LocallyOfFinitePresentation g]
    [IrreducibleSpace X] [NoetherianSpace X]
    (hetale : ∃ x : X, (g.stalkMap x).hom.FormallyEtale) :
    (schemeDivisorNonEtaleLocus g).Finite :=
  schemeDivisorNonEtaleLocus_finite_of_isClosed_of_exists_formallyEtale g
    (isClosed_schemeNonEtaleLocus g) hetale

end Pcf
