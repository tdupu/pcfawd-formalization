/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingProjectiveFormsFinite
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Artinian

/-!
# Finite surjective endomorphisms of projective space given by forms

The projective scheme `Proj K[x_0, …, x_N]` is integral, and the morphism
defined by basepoint-free homogeneous forms of common positive degree is
finite, dominant and surjective. This is the general layer for the projective
maps of `paper.tex`, Section `sec:examples`: `ex:squaring-PN`, `ex:koch` and
`ex:dupont` are instances.
-/

@[expose] public section
namespace Pcf.PaperCharZero
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
attribute [local instance] specializationOrder

/-- Stacks Lemma 29.21.8, implication `(1) ⇒ (2)`: the scheme fibers of
a locally quasi-finite morphism are discrete.

Divergence from Stacks: this declaration is only the indicated forward
implication of the three-way equivalence. -/
@[stacks 06RT "(1) ⇒ (2)"]
theorem schemeHom_discreteFibers_of_locallyQuasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hf : LocallyQuasiFinite f) : ∀ y : Y, DiscreteTopology (f.fiber y) := by
  let := hf
  intro y
  infer_instance

/-- Discrete fibers prevent a locally quasi-finite map from collapsing a
strict specialization. -/
theorem schemeHom_strictMono_of_locallyQuasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f] :
    StrictMono f := by
  intro x y hxy
  have hmono := f.continuous.specialization_monotone
  refine lt_of_le_not_ge (hmono hxy.le) ?_
  intro hyx
  have heq : f x = f y := le_antisymm (hmono hxy.le) hyx
  let := schemeHom_discreteFibers_of_locallyQuasiFinite f inferInstance (f x)
  have hdisc : _root_.IsDiscrete (f ⁻¹' {f x}) := by
    simpa [Scheme.Hom.range_fiberι] using
      (isDiscrete_univ_iff.mpr inferInstance).image (f.fiberι (f x)).isEmbedding.toIsInducing
  have hpoints : y = x := hdisc.eq_of_specializes
    hxy.le (by simpa using heq.symm) rfl
  exact hxy.ne hpoints.symm

/-- A locally quasi-finite endomorphism of an irreducible scheme of finite
specialization dimension fixes its generic point. -/
theorem genericPoint_map_eq_of_locallyQuasiFinite
    {X : Scheme.{u}} [IrreducibleSpace X] [FiniteDimensionalOrder X]
    (f : X ⟶ X) [LocallyQuasiFinite f] [LocallyOfFiniteType f] :
    f (genericPoint X) = genericPoint X := by
  have hmono := schemeHom_strictMono_of_locallyQuasiFinite f
  have hheight := Order.height_le_height_apply_of_strictMono f hmono (genericPoint X)
  have hle : f (genericPoint X) ≤ genericPoint X := genericPoint_specializes _
  by_contra hne
  have hlt : f (genericPoint X) < genericPoint X := lt_of_le_of_ne hle hne
  have hfin : Order.height (f (genericPoint X)) < ⊤ := by
    rw [← WithBot.coe_lt_coe]
    exact (Order.height_le_krullDim _).trans_lt
      Order.krullDim_ne_top_of_finiteDimensionalOrder.lt_top
  exact (not_lt_of_ge hheight) (Order.height_strictMono hlt hfin)

/-- A locally quasi-finite endomorphism of an irreducible scheme of finite
specialization dimension is dominant. -/
theorem schemeHom_isDominant_of_locallyQuasiFinite
    {X : Scheme.{u}} [IrreducibleSpace X] [FiniteDimensionalOrder X]
    (f : X ⟶ X) [LocallyQuasiFinite f] [LocallyOfFiniteType f] : IsDominant f := by
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.Subset.antisymm (Set.subset_univ _)
  rw [← genericPoint_closure X]
  apply closure_mono
  intro x hx
  have heq : x = genericPoint X := Set.mem_singleton_iff.mp hx
  exact ⟨genericPoint X, (genericPoint_map_eq_of_locallyQuasiFinite f).trans heq.symm⟩

/-- A dominant morphism with closed image is surjective. In particular, a
finite dominant morphism is surjective. -/
theorem schemeHom_surjective_of_isDominant_of_isFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsDominant f] [IsFinite f] :
    Function.Surjective f := by
  have hclosed : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  have hdense : closure (Set.range f) = Set.univ := f.denseRange.closure_range
  intro y
  have hy : y ∈ closure (Set.range f) := hdense ▸ Set.mem_univ y
  rw [hclosed.closure_eq] at hy
  exact hy

variable {K : Type u} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "polyGrade" => MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K

/-- The zero homogeneous prime is an actual projective point, since the
irrelevant ideal contains a nonzero coordinate. -/
noncomputable def projGenericPoint : ProjectiveSpectrum polyGrade where
  asHomogeneousIdeal := ⊥
  isPrime := by change (⊥ : Ideal (MvPolynomial (Fin n ⊕ Unit) K)).IsPrime; infer_instance
  not_irrelevant_le h := by
    have hx := h (HomogeneousIdeal.mem_irrelevant_of_mem polyGrade Nat.zero_lt_one
      (isHomogeneous_X K (Sum.inr ())))
    change (X (Sum.inr ()) : MvPolynomial (Fin n ⊕ Unit) K) = 0 at hx
    exact X_ne_zero (Sum.inr ()) hx

/-- The zero homogeneous prime specializes to every projective point. -/
theorem projGenericPoint_closure :
    closure ({projGenericPoint (K := K) (n := n)} :
      Set (ProjectiveSpectrum polyGrade)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  apply (ProjectiveSpectrum.le_iff_mem_closure polyGrade projGenericPoint x).mp
  change (⊥ : HomogeneousIdeal polyGrade) ≤ x.asHomogeneousIdeal
  exact bot_le

instance proj_irreducibleSpace :
    IrreducibleSpace (AlgebraicGeometry.Proj polyGrade) := by
  change IrreducibleSpace (ProjectiveSpectrum polyGrade)
  rw [irreducibleSpace_def]
  change IsIrreducible (Set.univ : Set (ProjectiveSpectrum polyGrade))
  rw [← projGenericPoint_closure (K := K) (n := n)]
  exact isIrreducible_singleton.closure

/-- Each homogeneous localization of the polynomial ring is reduced, being
a subring of an ordinary localization of a domain. -/
instance proj_away_isReduced (f : MvPolynomial (Fin n ⊕ Unit) K) :
    _root_.IsReduced (Away polyGrade f) := by
  have hinj : Function.Injective
      (algebraMap (Away polyGrade f) (Localization.Away f)) := by
    intro a b h
    exact HomogeneousLocalization.val_injective _ (by simpa using h)
  exact isReduced_of_injective _ hinj

/-- The standard affine charts `D₊(x_b)` as an open cover. -/
noncomputable def projCoordinateOpenCover :
    (AlgebraicGeometry.Proj polyGrade).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin n ⊕ Unit)
    (fun b => Spec (CommRingCat.of (Away polyGrade (MvPolynomial.X b))))
    (fun b => AlgebraicGeometry.Proj.awayι polyGrade (MvPolynomial.X b) (isHomogeneous_X K b)
      Nat.zero_lt_one) (by
      intro x
      obtain ⟨b, hb⟩ := Opens.mem_iSup.mp
        ((projSourceCoordinates_basicOpen_cover (K := K) (n := n)).ge (Set.mem_univ x))
      have hx : x ∈ (AlgebraicGeometry.Proj.awayι polyGrade (MvPolynomial.X b)
          (isHomogeneous_X K b) Nat.zero_lt_one).opensRange := by
        rw [AlgebraicGeometry.Proj.opensRange_awayι]
        exact hb
      obtain ⟨p, hp⟩ := hx
      exact ⟨b, p, hp⟩)

instance proj_isReduced : IsReduced (AlgebraicGeometry.Proj polyGrade) := by
  apply (IsReduced.iff_of_openCover _ (projCoordinateOpenCover (K := K) (n := n))).mpr
  intro b
  change AlgebraicGeometry.IsReduced
    (Spec (CommRingCat.of (Away polyGrade (MvPolynomial.X b : MvPolynomial (Fin n ⊕ Unit) K))))
  infer_instance

/-- The integrality part of Stacks Lemma 33.34.1's assertion that projective
space over a field is a variety.

Divergence from Stacks: only integrality is asserted here. -/
@[stacks 0B2P "integrality part of the variety assertion"]
instance proj_isIntegral : IsIntegral (AlgebraicGeometry.Proj polyGrade) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- Forgetting homogeneity embeds the specialization order of projective
points into the dual inclusion order of polynomial prime ideals. -/
noncomputable def projPrimeOrderEmbedding :
    (AlgebraicGeometry.Proj polyGrade) ↪o
      (PrimeSpectrum (MvPolynomial (Fin n ⊕ Unit) K))ᵒᵈ where
  toFun x := ⟨x.asHomogeneousIdeal.toIdeal, x.isPrime⟩
  inj' := by
    intro x y h
    apply ProjectiveSpectrum.ext
    exact HomogeneousIdeal.toIdeal_injective (PrimeSpectrum.ext_iff.mp h)
  map_rel_iff' := by
    intro x y
    change y.asHomogeneousIdeal ≤ x.asHomogeneousIdeal ↔ y ⤳ x
    rw [specializes_iff_mem_closure]
    exact ProjectiveSpectrum.le_iff_mem_closure polyGrade y x

/-- The actual projective scheme has finite specialization dimension. -/
instance proj_finiteDimensionalOrder :
    FiniteDimensionalOrder (AlgebraicGeometry.Proj polyGrade) := by
  apply Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mpr
  constructor
  · exact Order.krullDim_ne_bot_iff.mpr inferInstance
  · have hbound := Order.krullDim_le_of_strictMono _
      (projPrimeOrderEmbedding (K := K) (n := n)).strictMono
    have hpoly : Order.krullDim (PrimeSpectrum (MvPolynomial (Fin n ⊕ Unit) K))ᵒᵈ < ⊤ := by
      rw [Order.krullDim_orderDual]
      change ringKrullDim (MvPolynomial (Fin n ⊕ Unit) K) < ⊤
      simp only [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
        ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card, Fintype.card_sum,
        Fintype.card_fin, Fintype.card_unit, zero_add]
      rw [Nat.cast_add, Nat.cast_one]
      change ((n : ℕ∞) + 1 : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞)
      exact WithBot.coe_lt_coe.mpr (by simp)
    exact ne_top_of_lt (hbound.trans_lt hpoly)

variable (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
  (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
  (hcover : FormsCoverProjective F)

/-- Every basepoint-free positive-degree family of homogeneous forms
defines a dominant global projective scheme morphism. -/
instance projFormsProjective_isDominant :
    IsDominant (projFormsProjectiveSchemeMap F d hd hF hcover) :=
  schemeHom_isDominant_of_locallyQuasiFinite _

/-- Every basepoint-free positive-degree family of homogeneous forms
defines a surjective global projective scheme morphism. -/
theorem projFormsProjective_surjective :
    Function.Surjective (projFormsProjectiveSchemeMap F d hd hF hcover) :=
  schemeHom_surjective_of_isDominant_of_isFinite _

/-- The general layer: basepoint-free homogeneous forms of a common positive
degree define an actual finite surjective endomorphism of projective space. -/
theorem projFormsProjective_isFinite_surjective :
    IsFinite (projFormsProjectiveSchemeMap F d hd hF hcover) ∧
      Function.Surjective (projFormsProjectiveSchemeMap F d hd hF hcover) :=
  ⟨inferInstance, projFormsProjective_surjective F d hd hF hcover⟩

/-- A sufficient criterion for basepoint-freeness: some positive power of each
coordinate lies in the ideal generated by the forms. -/
theorem formsCoverProjective_of_pow_mem (e : ℕ)
    (he : ∀ i, (X i : MvPolynomial (Fin n ⊕ Unit) K) ^ e ∈ Ideal.span (Set.range F)) :
    FormsCoverProjective F := by
  refine (projCoordinatePowers_cover (K := K) (n := n) e).trans ?_
  apply Ideal.radical_mono
  rw [Ideal.span_le, Set.range_subset_iff]
  exact he

#print axioms schemeHom_strictMono_of_locallyQuasiFinite
#print axioms schemeHom_isDominant_of_locallyQuasiFinite
#print axioms schemeHom_surjective_of_isDominant_of_isFinite
#print axioms proj_irreducibleSpace
#print axioms proj_isReduced
#print axioms proj_isIntegral
#print axioms proj_finiteDimensionalOrder
#print axioms projFormsProjective_isDominant
#print axioms projFormsProjective_surjective
#print axioms projFormsProjective_isFinite_surjective
#print axioms formsCoverProjective_of_pow_mem
end Pcf.PaperCharZero
