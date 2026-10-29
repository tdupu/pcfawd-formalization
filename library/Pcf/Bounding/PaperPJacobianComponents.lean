/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPJacobianWeighted
public import Pcf.Bounding.PaperPComponents

/-!
# Codimension-one components of the homogeneous Jacobian zero locus

Components are maximal irreducible subsets, with codimension measured at
their unique generic point. The final equality uses the actual normalized
weighted critical locus. Finiteness and dominance of the constructed
positive-degree map are proved in the imported geometry modules.
-/

@[expose] public section
namespace Pcf
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- The irreducible components of a closed locus that have codimension
one in the ambient scheme, measured at their generic point. -/
def codimensionOneRelativeIrreducibleComponents {X : Scheme.{u}} (Z : Set X) : Set (Set X) :=
  {D | D ∈ relativeIrreducibleComponents Z ∧
    ∃ x : SchemeDivisorPoint X, IsGenericPoint x.1 D}

/-- A codimension-one point in a proper closed subset of an irreducible
scheme is the generic point of an irreducible component of that subset. -/
theorem closure_singleton_mem_relativeIrreducibleComponents
    {X : Scheme.{u}} [IrreducibleSpace X] {Z : Set X}
    (hZ : IsClosed Z) (hproper : Z ≠ Set.univ) {x : X}
    (hxZ : x ∈ Z) (hx : Order.coheight x = 1) :
    closure ({x} : Set X) ∈ relativeIrreducibleComponents Z := by
  refine ⟨⟨isIrreducible_singleton.closure,
    closure_minimal (Set.singleton_subset_iff.mpr hxZ) hZ⟩, ?_⟩
  intro D hD hxD
  let y := hD.1.genericPoint
  have hy : IsGenericPoint y (closure D) := hD.1.isGenericPoint_genericPoint_closure
  have hyZ : y ∈ Z := (closure_minimal hD.2 hZ) hy.mem
  have hxy : x ≤ y := hy.specializes (subset_closure (hxD (subset_closure (by simp))))
  have hylt : y < genericPoint X :=
    QuasiSober.val_lt_genericPoint_of_closure_ne_univ
      (by simpa only [hZ.closure_eq] using hproper) ⟨y, hyZ⟩
  have hypos : (1 : ℕ∞) ≤ Order.coheight y := by
    have hfirst : (1 : ℕ∞) ≤ Order.coheight (genericPoint X) + 1 :=
      by simp
    exact hfirst.trans (Order.coheight_add_one_le hylt)
  have hyeq : y = x := by
    by_contra hne
    have hlt : x < y := lt_of_le_not_ge hxy fun hyx =>
      hne (Specializes.antisymm hxy hyx).eq
    have htwo : (2 : ℕ∞) ≤ Order.coheight x := calc
      2 = 1 + 1 := rfl
      _ ≤ Order.coheight y + 1 := add_le_add hypos le_rfl
      _ ≤ Order.coheight x := Order.coheight_add_one_le hlt
    rw [hx] at htwo
    norm_num at htwo
  rw [hyeq] at hy
  rw [hy.def]
  exact subset_closure

/-- The codimension-one components of a proper closed subset are exactly
the closures of its codimension-one points. -/
theorem codimensionOneRelativeIrreducibleComponents_eq
    {X : Scheme.{u}} [IrreducibleSpace X] {Z : Set X}
    (hZ : IsClosed Z) (hproper : Z ≠ Set.univ) :
    codimensionOneRelativeIrreducibleComponents Z =
      (fun x : X => closure ({x} : Set X)) '' {x | x ∈ Z ∧ Order.coheight x = 1} := by
  ext D
  constructor
  · rintro ⟨hD, x, hx⟩
    exact ⟨x.1, ⟨hD.1.2 hx.mem, x.2⟩, hx.def⟩
  · rintro ⟨x, ⟨hxZ, hx⟩, rfl⟩
    exact ⟨closure_singleton_mem_relativeIrreducibleComponents hZ hproper hxZ hx,
      ⟨⟨x, hx⟩, isGenericPoint_closure⟩⟩

/-- Taking the union of the codimension-one components agrees with the
closure of the codimension-one points on a proper closed Noetherian locus. -/
theorem sUnion_codimensionOneRelativeIrreducibleComponents_eq_closure
    {X : Scheme.{u}} [IrreducibleSpace X] [NoetherianSpace X] {Z : Set X}
    (hZ : IsClosed Z) (hproper : Z ≠ Set.univ) :
    ⋃₀ codimensionOneRelativeIrreducibleComponents Z =
      closure {x : X | x ∈ Z ∧ Order.coheight x = 1} := by
  let : QuasiSober Z := hZ.isClosedEmbedding_subtypeVal.quasiSober
  have hfin : {x ∈ Z | Order.coheight x = 1}.Finite :=
    NoetherianSpace.finite_coheight_one_of_closure_ne_univ
      (by simpa only [hZ.closure_eq] using hproper)
  rw [codimensionOneRelativeIrreducibleComponents_eq hZ hproper]
  symm
  calc
    closure {x : X | x ∈ Z ∧ Order.coheight x = 1} =
        closure (⋃ x ∈ {x : X | x ∈ Z ∧ Order.coheight x = 1}, ({x} : Set X)) := by
      rw [Set.biUnion_of_singleton]
    _ = ⋃ x ∈ {x : X | x ∈ Z ∧ Order.coheight x = 1}, closure ({x} : Set X) :=
      hfin.closure_biUnion _
    _ = _ := by ext x; simp

variable {K : Type u} [Field K] [CharZero K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "polyGrade" => MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K

local instance : IsIso (Palomar.normalizationMap
    (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K))) :=
  normalScheme_normalizationMap_isIso
    (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K))

variable (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
  (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
  (hcover : PaperPFormsCoverProjective F)

include d hd hF hcover in
/-- A finite dominant projective endomorphism in characteristic zero has
a proper homogeneous Jacobian zero locus. -/
theorem paperPFormsProjective_jacobian_zeroLocus_ne_univ :
    ProjectiveSpectrum.zeroLocus polyGrade
      {Matrix.det (fun i j => pderiv j (F i))} ≠ Set.univ := by
  have : CharZero ((AlgebraicGeometry.Proj polyGrade).presheaf.stalk
      (genericPoint (AlgebraicGeometry.Proj polyGrade))) := paperPProjective_stalk_charZero _
  have hgen := formallyEtale_stalkMap_genericPoint_of_finite_dominant_charZero
    (paperPFormsProjectiveSchemeMap F d hd hF hcover)
  rw [← paperPFormsProjective_nonEtaleLocus_eq_zeroLocus F d hd hF hcover
    (Nat.cast_ne_zero.mpr hd.ne')]
  intro h
  exact (h.symm ▸ Set.mem_univ (genericPoint (AlgebraicGeometry.Proj polyGrade))) hgen

/-- The final assertion of the homogeneous Jacobian lemma: in
characteristic zero the actual normalized weighted critical locus is the
union of the codimension-one components of the homogeneous Jacobian zero
locus. The geometric and map properties are concrete proved instances.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
theorem paperPFormsProjective_normalizedCriticalLocus_eq_components :
    weightedCriticalLocus (paperPFormsProjectiveSchemeMap F d hd hF hcover) =
      ⋃₀ codimensionOneRelativeIrreducibleComponents
        (ProjectiveSpectrum.zeroLocus polyGrade
          {Matrix.det (fun i j => pderiv j (F i))}) := by
  rw [sUnion_codimensionOneRelativeIrreducibleComponents_eq_closure
    (ProjectiveSpectrum.isClosed_zeroLocus _ _)
    (paperPFormsProjective_jacobian_zeroLocus_ne_univ F d hd hF hcover)]
  rw [paperPFormsProjective_normalizedCriticalLocus_eq_closure F d hd hF hcover
    (Nat.cast_ne_zero.mpr hd.ne')]
  congr 1
  ext x
  change (Order.coheight x = 1 ∧
    Matrix.det (fun i j => pderiv j (F i)) ∈ x.asHomogeneousIdeal) ↔
    (({Matrix.det (fun i j => pderiv j (F i))} : Set (MvPolynomial (Fin n ⊕ Unit) K)) ⊆
      (x.asHomogeneousIdeal : Set (MvPolynomial (Fin n ⊕ Unit) K)) ∧ Order.coheight x = 1)
  simp only [Set.singleton_subset_iff]
  exact and_comm

#print axioms codimensionOneRelativeIrreducibleComponents
#print axioms closure_singleton_mem_relativeIrreducibleComponents
#print axioms codimensionOneRelativeIrreducibleComponents_eq
#print axioms sUnion_codimensionOneRelativeIrreducibleComponents_eq_closure
#print axioms paperPFormsProjective_jacobian_zeroLocus_ne_univ
#print axioms paperPFormsProjective_normalizedCriticalLocus_eq_components
end Pcf
