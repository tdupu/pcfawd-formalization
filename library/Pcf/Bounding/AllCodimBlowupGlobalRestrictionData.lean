/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupGlobalNormalizedData
public import Pcf.Bounding.PaperPBlowupComponentSquare
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.Ideal.GoingDown

/-!
# Blow-up restriction data on the global normalized blow-up

`latex/paper-p.tex`, Definition `def:blowup-restriction-data`, fixes normalized blow-up data
`(f : X → Y, A, B, X', Y', α, β)`, the finite lift `f' : X' → Y'`, the restriction
`g = f|_A : A → B`, an irreducible component `A'` of `α⁻¹(A)` dominating `A`, and the reduced
closed image `B' = f'(A')`. The first sentence of Proposition `prop:bound-blowup` says that `B'` is
an irreducible component of `β⁻¹(B)` dominating `B`.

This file encodes these data on the actual global normalized blow-ups
`X' = globalNormalizedBlowup ((pointCentre b).comap f)` and
`Y' = globalNormalizedBlowup (pointCentre b)`, where `pointCentre b` is the reduced ideal sheaf
of `B = closure {b}`. For `b = f a` this is definitionally the centre `blowupCentre f a` of
`AllCodimBlowupGlobalNormalizedData`. Components are encoded by their generic points, following
`divisorPoint_irreducibleComponent_of_proper_closed`: the closure of the generic point is an
irreducible component of the closed set, as a subspace. All four varieties `A, B, A', B'` are the
canonical reduced point closures `(pointClosureIdealSheaf _).subscheme`.

Main results:

* `globalReesToBase_isProper`, `globalNormalizedBlowupToBase_isProper`: `β` is proper.
* `generalizingMap_of_isFinite_of_isNormalScheme`: going down for finite dominant morphisms of
  integral schemes with normal target (`@[stacks 00H8]` in Mathlib, globalized here).
* `BlowupRestrictionData`: the data of `def:blowup-restriction-data`.
* `BlowupRestrictionData.nonempty`: such components `A'` exist.
* `BlowupRestrictionData.image_isComponent`: `B'` is an irreducible component of `β⁻¹(B)`
  dominating `B`.
* `BlowupRestrictionData.square`: the comparison square of the restricted maps.
-/

@[expose] public section
namespace Pcf.Bounding.AllCodimBlowup
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u
noncomputable section

/-! ## Components of closed sets, by generic points -/

section Components

variable {T : Type*} [TopologicalSpace T]

/-- A generization, inside a closed set, of the generic point of one of its irreducible
components is that generic point. -/
theorem eq_of_specializes_of_mem_irreducibleComponents [T0Space T] {E : Set T} {v : T}
    (hv : v ∈ E) (hC : closure {(⟨v, hv⟩ : E)} ∈ irreducibleComponents E) {y : T} (hy : y ∈ E)
    (hyv : y ⤳ v) : y = v := by
  have hyv' : (⟨y, hy⟩ : E) ⤳ ⟨v, hv⟩ := IsInducing.subtypeVal.specializes_iff.mp hyv
  have hsub : closure {(⟨v, hv⟩ : E)} ⊆ closure {(⟨y, hy⟩ : E)} := by
    apply closure_minimal _ isClosed_closure
    rintro _ rfl
    exact specializes_iff_mem_closure.mp hyv'
  have hle := hC.2 isIrreducible_singleton.closure hsub
  have hvy : (⟨v, hv⟩ : E) ⤳ ⟨y, hy⟩ :=
    specializes_iff_mem_closure.mpr (hle (subset_closure rfl))
  exact congrArg Subtype.val (hyv'.antisymm hvy).eq

/-- In a closed subset of a quasi-sober space, every point specializes from the generic point of
an irreducible component of that subset. -/
theorem exists_specializes_mem_irreducibleComponents [QuasiSober T] {E : Set T} (hE : IsClosed E)
    {x : T} (hx : x ∈ E) :
    ∃ (v : T) (hv : v ∈ E), v ⤳ x ∧ closure {(⟨v, hv⟩ : E)} ∈ irreducibleComponents E := by
  haveI : QuasiSober E := hE.isClosedEmbedding_subtypeVal.quasiSober
  obtain ⟨C, hC, hsub⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible ({⟨x, hx⟩} : Set E)
      isIrreducible_singleton
  have hCcl : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  have hgen : closure {hC.1.genericPoint} = C := by
    have h := hC.1.isGenericPoint_genericPoint_closure
    rw [hCcl.closure_eq] at h
    exact h
  refine ⟨hC.1.genericPoint.1, hC.1.genericPoint.2, ?_, ?_⟩
  · have hmem : (⟨x, hx⟩ : E) ∈ closure {hC.1.genericPoint} := by
      rw [hgen]
      exact hsub rfl
    exact (specializes_iff_mem_closure.mpr hmem).map continuous_subtype_val
  · simpa only [Subtype.coe_eta, hgen] using hC

/-- A point of a closed set none of whose proper generizations lie in the set is the generic
point of an irreducible component of the set. -/
theorem mem_irreducibleComponents_of_forall_specializes [QuasiSober T] [T0Space T] {E : Set T}
    (hE : IsClosed E) {v : T} (hv : v ∈ E) (hmax : ∀ y ∈ E, y ⤳ v → y = v) :
    closure {(⟨v, hv⟩ : E)} ∈ irreducibleComponents E := by
  obtain ⟨w, hw, hwv, hC⟩ := exists_specializes_mem_irreducibleComponents hE hv
  obtain rfl := hmax w hw hwv
  exact hC

end Components

/-! ## Going down for finite morphisms to normal schemes -/

/-- Going down for a finite dominant morphism of integral schemes with normal target: every
generization of an image point lifts to a generization. This is Mathlib's affine going down for
integral extensions of an integrally closed domain (Stacks 00H8), globalized over affine opens.

`paper-p.tex` correspondence: Definition 7.10 (`def:blowup-restriction-data`). -/
theorem generalizingMap_of_isFinite_of_isNormalScheme {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsNormalScheme Y] (f : X ⟶ Y) [IsFinite f] [IsDominant f] :
    GeneralizingMap f := by
  intro x y hy
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  let W : Y.affineOpens := ⟨U, hU⟩
  let V : X.affineOpens := finitePreimageAffine f W
  have hyU : y ∈ U := hy.mem_open U.isOpen hxU
  have hxV : x ∈ (V : X.Opens) := hxU
  haveI : Nonempty (W : Y.Opens) := ⟨⟨y, hyU⟩⟩
  haveI : Nonempty (V : X.Opens) := ⟨⟨x, hxV⟩⟩
  letI : Algebra Γ(Y, W) Γ(X, V) := (f.app U).hom.toAlgebra
  haveI : Module.Finite Γ(Y, W) Γ(X, V) := moduleFinite_finitePreimageAffine f W
  haveI : FaithfulSMul Γ(Y, W) Γ(X, V) := faithfulSMul_finitePreimageAffine f W
  haveI : IsIntegrallyClosed Γ(Y, W) := IsNormalScheme.component_integrallyClosed W
  haveI : Algebra.IsIntegral Γ(Y, W) Γ(X, V) := Algebra.IsIntegral.of_finite _ _
  have hgd : GeneralizingMap (PrimeSpectrum.comap (algebraMap Γ(Y, W) Γ(X, V))) :=
    Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp inferInstance
  have hsq : Spec.map (f.app U) ≫ W.2.fromSpec = V.2.fromSpec ≫ f := by
    rw [Scheme.Hom.app_eq_appLE]
    exact IsAffineOpen.SpecMap_appLE_fromSpec f W.2 V.2 _
  have hsq' : ∀ z, W.2.fromSpec (PrimeSpectrum.comap (algebraMap Γ(Y, W) Γ(X, V)) z) =
      f (V.2.fromSpec z) := fun z ↦ by
    have := congrArg (fun m ↦ m z) hsq
    simp only [Scheme.Hom.comp_apply] at this
    exact this
  obtain ⟨x', rfl⟩ : x ∈ Set.range V.2.fromSpec := by rw [V.2.range_fromSpec]; exact hxV
  obtain ⟨y', rfl⟩ : y ∈ Set.range W.2.fromSpec := by rw [W.2.range_fromSpec]; exact hyU
  have hy' : y' ⤳ PrimeSpectrum.comap (algebraMap Γ(Y, W) Γ(X, V)) x' := by
    rw [← W.2.fromSpec.isOpenEmbedding.isInducing.specializes_iff, hsq']
    exact hy
  obtain ⟨z', hz', hzeq⟩ := hgd hy'
  refine ⟨V.2.fromSpec z', hz'.map V.2.fromSpec.continuous, ?_⟩
  rw [← hsq', hzeq]

/-! ## Properness of the normalized blow-up -/

section Proper

variable {Y : Scheme.{u}}

/-- The global Rees blow-up of a locally Noetherian scheme is proper over it: properness is local
on the target, and each affine chart is the projective Rees `Proj` of a finitely generated ideal.

Divergence from Stacks: Stacks proves the blow-up in a finite-type ideal is projective; this
records only the resulting properness, and assumes the base locally Noetherian so that every
ideal of the sheaf is finitely generated.

`paper-p.tex` correspondence: Definition 7.10 (`def:blowup-restriction-data`). -/
@[stacks 02NS "(1), properness only"]
theorem globalReesToBase_isProper [IsLocallyNoetherian Y] (I : Y.IdealSheafData) :
    IsProper (globalReesToBase I) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsProper) Y.directedAffineCover]
  intro U
  have h := (globalReesChart_isPullback I U).flip
  haveI : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian U
  have hfg : (I.ideal U).FG := IsNoetherian.noetherian _
  letI : IsProper (reesProjToSpec (I.ideal U)) := reesProjToSpec_isProper' _ hfg
  change IsProper (pullback.snd (globalReesToBase I) U.1.ι)
  rw [← h.isoPullback_inv_snd]
  dsimp only [affineReesToOpen]
  infer_instance

variable [IsIntegral Y] (I : Y.IdealSheafData) [Fact (genericPoint Y ∉ I.support)]

/-- The natural map `β : Y' ⟶ Y` of the normalized blow-up is proper over a scheme locally of
finite type over a field. -/
theorem globalNormalizedBlowupToBase_isProper (k : Type u) [Field k] (s : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType s] : IsProper (globalNormalizedBlowupToBase I) := by
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  haveI := globalReesToBase_isProper I
  haveI := globalRees_normalizationMap_isFinite I k s
  dsimp only [globalNormalizedBlowupToBase]
  infer_instance

/-- The natural map `β : Y' ⟶ Y` is surjective. -/
theorem globalNormalizedBlowupToBase_surjective (k : Type u) [Field k] (s : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType s] : Function.Surjective (globalNormalizedBlowupToBase I) := by
  haveI := globalNormalizedBlowupToBase_isProper I k s
  exact (surjective_of_isDominant_of_isClosed_range (globalNormalizedBlowupToBase I)
    (globalNormalizedBlowupToBase I).isClosedMap.isClosed_range).surj

end Proper

/-! ## The restriction data -/

section Data

variable {X Y : Scheme.{u}}

/-- The reduced centre `B = closure {b}` on `Y`. For `b = f a` this is definitionally
`blowupCentre f a`. -/
abbrev pointCentre (b : Y) : Y.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨closure {b}, isClosed_closure⟩

theorem blowupCentre_eq_pointCentre (f : X ⟶ Y) (a : X) :
    blowupCentre f a = pointCentre (f a) := rfl

theorem pointCentre_support (b : Y) :
    ((pointCentre b).support : Set Y) = closure {b} :=
  Scheme.IdealSheafData.coe_support_vanishingIdeal _

/-- The centre `B = f(A)` of a proper integral closed subvariety `A ⊊ X` misses the generic
point of `Y`. -/
theorem fact_genericPoint_not_mem_pointCentre [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [IsFinite f] [IsDominant f] (a : X) (ha : a ≠ genericPoint X) (b : Y) (hab : f a = b) :
    Fact (genericPoint Y ∉ (pointCentre b).support) := by
  subst hab
  exact ⟨genericPoint_not_mem_blowupCentre f a ha⟩

variable [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsFinite f] [IsDominant f]

/-- `latex/paper-p.tex`, Definition `def:blowup-restriction-data`, on the global normalized
blow-ups `X' = globalNormalizedBlowup ((pointCentre b).comap f)` and
`Y' = globalNormalizedBlowup (pointCentre b)`. The subvariety `A ⊊ X` is the closure of `a`, with
`B = f(A) = closure {b}`. The component `A'` of `α⁻¹(A)` is recorded by its generic point
`point`: its closure is an irreducible component of `α⁻¹(A)` (as a subspace), and `A'` dominates
`A`, that is `α point = a`. The restricted maps and `B' = f'(A')` are defined below.

`paper-p.tex` correspondence: Definition 7.10 (`def:blowup-restriction-data`). -/
structure BlowupRestrictionData (a : X) (b : Y) [Fact (genericPoint Y ∉ (pointCentre b).support)]
    where
  /-- `A ⊊ X`. -/
  ne_genericPoint : a ≠ genericPoint X
  /-- `B = f(A)`. -/
  map_centre : f a = b
  /-- The generic point of `A'`. -/
  point : globalNormalizedBlowup ((pointCentre b).comap f)
  /-- `A'` dominates `A`. -/
  dominates : globalNormalizedBlowupToBase ((pointCentre b).comap f) point = a
  /-- `A'` is an irreducible component of `α⁻¹(A)`. -/
  isComponent : ∀ h : point ∈ globalNormalizedBlowupToBase ((pointCentre b).comap f) ⁻¹'
      closure {a}, closure {(⟨point, h⟩ :
        globalNormalizedBlowupToBase ((pointCentre b).comap f) ⁻¹' closure {a})} ∈
      irreducibleComponents
        (globalNormalizedBlowupToBase ((pointCentre b).comap f) ⁻¹' closure {a})

namespace BlowupRestrictionData

variable {f} {a : X} {b : Y} [Fact (genericPoint Y ∉ (pointCentre b).support)]
  (D : BlowupRestrictionData f a b)

/-- `α : X' ⟶ X`. -/
abbrev α (f : X ⟶ Y) [IsFinite f] [IsDominant f] (b : Y)
    [Fact (genericPoint Y ∉ (pointCentre b).support)] :
    globalNormalizedBlowup ((pointCentre b).comap f) ⟶ X :=
  globalNormalizedBlowupToBase ((pointCentre b).comap f)

/-- `β : Y' ⟶ Y`. -/
abbrev β (b : Y) [Fact (genericPoint Y ∉ (pointCentre b).support)] :
    globalNormalizedBlowup (pointCentre b) ⟶ Y :=
  globalNormalizedBlowupToBase (pointCentre b)

/-- `f' : X' ⟶ Y'`. -/
abbrev lift (f : X ⟶ Y) [IsFinite f] [IsDominant f] (b : Y)
    [Fact (genericPoint Y ∉ (pointCentre b).support)] :
    globalNormalizedBlowup ((pointCentre b).comap f) ⟶ globalNormalizedBlowup (pointCentre b) :=
  globalNormalizedBlowupMap f (pointCentre b)

theorem lift_comm : lift f b ≫ β b = α f b ≫ f :=
  globalNormalizedBlowupMap_comm f (pointCentre b)

/-- The generic point of `B' = f'(A')`. -/
abbrev imagePoint : globalNormalizedBlowup (pointCentre b) := lift f b D.point

/-- `B'` dominates `B`: `β` maps the generic point of `B'` to `b`. -/
theorem β_imagePoint : β b D.imagePoint = b := by
  have h := congrArg (fun m ↦ m D.point) (lift_comm (f := f) (b := b))
  simp only [Scheme.Hom.comp_apply] at h
  rw [h, D.dominates, D.map_centre]

/-- `A = closure {a}`, reduced. -/
abbrev A (_ : BlowupRestrictionData f a b) : Scheme.{u} := (pointClosureIdealSheaf a).subscheme
/-- `B = closure {b}`, reduced. -/
abbrev B (_ : BlowupRestrictionData f a b) : Scheme.{u} := (pointClosureIdealSheaf b).subscheme
/-- `A'`, the reduced closure of `point`. -/
abbrev A' : Scheme.{u} := (pointClosureIdealSheaf D.point).subscheme
/-- `B' = f'(A')`, the reduced closure of `imagePoint`. -/
abbrev B' : Scheme.{u} := (pointClosureIdealSheaf D.imagePoint).subscheme

/-- `g = f|_A : A ⟶ B`. -/
abbrev g : D.A ⟶ D.B := pointClosureSubschemeMap f a b D.map_centre
/-- `f'|_{A'} : A' ⟶ B'`. -/
abbrev liftRestrict : D.A' ⟶ D.B' := pointClosureSubschemeMap (lift f b) D.point D.imagePoint rfl
/-- `α|_{A'} : A' ⟶ A`. -/
abbrev αRestrict : D.A' ⟶ D.A := pointClosureSubschemeMap (α f b) D.point a D.dominates
/-- `q = β|_{B'} : B' ⟶ B`. -/
abbrev q : D.B' ⟶ D.B := pointClosureSubschemeMap (β b) D.imagePoint b D.β_imagePoint

/-- The comparison square `q ∘ f'|_{A'} = g ∘ α|_{A'}` of the restricted maps. -/
@[reassoc]
theorem square : D.liftRestrict ≫ D.q = D.αRestrict ≫ D.g := by
  apply (cancel_mono (pointClosureIdealSheaf b).subschemeι).mp
  simp only [Category.assoc, pointClosureSubschemeMap_subschemeι,
    pointClosureSubschemeMap_subschemeι_assoc, lift_comm]

instance g_isFinite : IsFinite D.g := pointClosureSubschemeMap_isFinite _ _ _ _
instance g_isDominant : IsDominant D.g := pointClosureSubschemeMap_isDominant _ _ _ _
instance αRestrict_isDominant : IsDominant D.αRestrict :=
  pointClosureSubschemeMap_isDominant _ _ _ _
instance q_isDominant : IsDominant D.q := pointClosureSubschemeMap_isDominant _ _ _ _
instance liftRestrict_isDominant : IsDominant D.liftRestrict :=
  pointClosureSubschemeMap_isDominant _ _ _ _

/-- `B' = f'(A')` is an irreducible component of `β⁻¹(B)`: this is the first sentence of
`latex/paper-p.tex`, Proposition `prop:bound-blowup`. The proof uses going down for the finite
lift `f'` to the normal scheme `Y'` and the absence of proper specializations in the fibres of
the finite map `f`, instead of the source's codimension-one argument. -/
theorem image_isComponent (k : Type u) [Field k] (s : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType s] :
    ∀ h : D.imagePoint ∈ β b ⁻¹' closure {b},
      closure {(⟨D.imagePoint, h⟩ : β b ⁻¹' closure {b})} ∈
        irreducibleComponents (β b ⁻¹' closure {b}) := by
  intro h
  haveI := globalNormalizedBlowupMap_isFinite f (pointCentre b) k s
  apply mem_irreducibleComponents_of_forall_specializes (isClosed_closure.preimage (β b).continuous)
  intro y hy hyv
  obtain ⟨z, hz, rfl⟩ := generalizingMap_of_isFinite_of_isNormalScheme (lift f b) hyv
  have hαz : α f b z ⤳ a := by
    have := hz.map (α f b).continuous
    rwa [D.dominates] at this
  have hfαz : f (α f b z) = b := by
    have h1 : f (α f b z) ∈ closure {b} := by
      have h := congrArg (fun m ↦ m z) (lift_comm (f := f) (b := b))
      simp only [Scheme.Hom.comp_apply] at h
      rw [← h]
      exact hy
    have h2 : f (α f b z) ⤳ b := by
      have := hαz.map f.continuous
      rwa [D.map_centre] at this
    exact (h2.antisymm (specializes_iff_mem_closure.mpr h1)).eq
  have hαza : α f b z = a := by
    by_contra hne
    letI := specializationOrder X
    letI := specializationOrder Y
    have hlt : a < α f b z := lt_of_le_of_ne (show a ≤ α f b z from hαz) (Ne.symm hne)
    have hmono := schemeHom_strictMono_of_locallyQuasiFinite f hlt
    rw [hfαz, D.map_centre] at hmono
    exact lt_irrefl _ hmono
  have hzmem : z ∈ α f b ⁻¹' closure {a} := by
    simp only [Set.mem_preimage, hαza]
    exact subset_closure rfl
  have hpt : D.point ∈ α f b ⁻¹' closure {a} := by
    simp only [Set.mem_preimage, D.dominates]
    exact subset_closure rfl
  rw [eq_of_specializes_of_mem_irreducibleComponents hpt (D.isComponent hpt) hzmem hz]

end BlowupRestrictionData

/-- Components `A'` as in `def:blowup-restriction-data` exist: since `α` is surjective, some
point of `X'` lies over `a`, and the generic point of an irreducible component of `α⁻¹(A)`
through it maps to `a`. -/
theorem BlowupRestrictionData.nonempty (k : Type u) [Field k] (s : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType s] (a : X) (ha : a ≠ genericPoint X) (b : Y) (hab : f a = b)
    [Fact (genericPoint Y ∉ (pointCentre b).support)] :
    Nonempty (BlowupRestrictionData f a b) := by
  let α := globalNormalizedBlowupToBase ((pointCentre b).comap f)
  obtain ⟨x₀, hx₀⟩ := globalNormalizedBlowupToBase_surjective ((pointCentre b).comap f) k (f ≫ s) a
  have hmem : x₀ ∈ α ⁻¹' closure {a} := by
    rw [Set.mem_preimage, hx₀]
    exact subset_closure rfl
  obtain ⟨v, hv, hvx, hC⟩ :=
    exists_specializes_mem_irreducibleComponents (isClosed_closure.preimage α.continuous) hmem
  have hva : α v = a := by
    have h1 : α v ⤳ a := by
      have := hvx.map α.continuous
      rwa [hx₀] at this
    exact (h1.antisymm (specializes_iff_mem_closure.mpr hv)).eq
  exact ⟨⟨ha, hab, v, hva, fun _ ↦ hC⟩⟩

#print axioms generalizingMap_of_isFinite_of_isNormalScheme
#print axioms globalNormalizedBlowupToBase_isProper
#print axioms BlowupRestrictionData.image_isComponent
#print axioms BlowupRestrictionData.nonempty
#print axioms BlowupRestrictionData.square

end Data

end
end Pcf.Bounding.AllCodimBlowup
