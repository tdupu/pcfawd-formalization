/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPDimensionFormula
public import Pcf.Bounding.AllCodimChartProofAffine
public import Pcf.Bounding.PaperPDimensionZeroKMorphism
public import Pcf.Bounding.PcfAllTheWayDownScheme

/-!
# The dimension drops by one along a divisor (`paper-p.tex`, l. 554–555)

An integral scheme locally of finite type over a field has the dimension of
each of its nonempty affine opens (closed points are dense and all have the
same codimension). With the affine formula
`ringKrullDim_quotient_add_one_of_height_eq_one` this gives
`dim B + 1 = dim X` for the reduced closure `B` of a codimension-one point.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

universe u

noncomputable section

set_option linter.style.haveILetI false

attribute [local instance] specializationOrder in
/-- An integral scheme locally of finite type over a field has the Krull
dimension of each nonempty affine open.

Divergence from Stacks: only the first clause of (3), for an integral (rather
than irreducible) scheme and for nonempty *affine* opens, with the dimension of
the open computed as the Krull dimension of its ring of sections. -/
@[stacks 0A21 "(3), first clause, for nonempty affine opens of an integral scheme"]
theorem topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen
    (k : Type u) [Field k] {Z : Scheme.{u}} [IsIntegral Z]
    (s : Z ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (W : Z.Opens) (hW : IsAffineOpen W) (hne : (W : Set Z).Nonempty) :
    topologicalKrullDim Z = ringKrullDim Γ(Z, W) := by
  haveI : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace s
  -- the common height of maximal ideals of an affine chart
  have hchart : ∀ (V : Z.Opens) (hV : IsAffineOpen V) (x : Z) (hx : x ∈ V),
      ∃ m : ℕ, ringKrullDim Γ(Z, V) = m ∧ Order.coheight x ≤ m ∧
        (IsClosed ({x} : Set Z) → Order.coheight x = m) := by
    intro V hV x hx
    haveI : Nonempty V := ⟨⟨x, hx⟩⟩
    letI := schemeAffineAlgebraOfField k s ⟨V, hV⟩
    haveI := schemeAffineAlgebraOfField_finiteType k s ⟨V, hV⟩
    obtain ⟨m, hm, hdim⟩ := finiteType_domain_height_maximal k Γ(Z, V)
    refine ⟨m, hdim, ?_, ?_⟩
    · rw [← affineOpen_primeIdealOf_height hV x hx]
      have := Ideal.height_le_ringKrullDim_of_isPrime
        (I := (hV.primeIdealOf ⟨x, hx⟩).asIdeal)
      rw [hdim] at this
      exact_mod_cast this
    · intro hcl
      rw [← affineOpen_primeIdealOf_height hV x hx]
      apply hm
      rw [← PrimeSpectrum.isClosed_singleton_iff_isMaximal]
      have : ({hV.primeIdealOf ⟨x, hx⟩} : Set (Spec Γ(Z, V))) = hV.fromSpec ⁻¹' {x} := by
        ext P
        simp only [Set.mem_singleton_iff, Set.mem_preimage]
        constructor
        · rintro rfl; exact hV.fromSpec_primeIdealOf ⟨x, hx⟩
        · intro h
          apply hV.fromSpec.isOpenEmbedding.injective
          rw [h, hV.fromSpec_primeIdealOf]
      have hc := hcl.preimage hV.fromSpec.continuous
      rw [← this] at hc
      exact hc
  obtain ⟨w, hwW, hwcl⟩ := nonempty_inter_closedPoints hne W.isOpen.isLocallyClosed
  obtain ⟨m, hdimW, -, hwm⟩ := hchart W hW w hwW
  have hw : Order.coheight w = m := hwm hwcl
  rw [hdimW, ← scheme_orderKrullDim_eq_topologicalKrullDim,
    Order.krullDim_eq_iSup_coheight_of_nonempty]
  congr 1
  apply le_antisymm
  · refine iSup_le fun x => ?_
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : Z.Opens) from trivial)
    obtain ⟨z, ⟨hzV, hzW⟩, hzcl⟩ := nonempty_inter_closedPoints
      (nonempty_preirreducible_inter V.isOpen W.isOpen ⟨x, hxV⟩ hne)
      (V.isOpen.inter W.isOpen).isLocallyClosed
    obtain ⟨mV, hdimV, hxle, -⟩ := hchart V hV x hxV
    obtain ⟨mV2, hdimV2, -, hzV2⟩ := hchart V hV z hzV
    obtain ⟨mW', hdimW', -, hzW'⟩ := hchart W hW z hzW
    have e1 : (mV : WithBot ℕ∞) = mV2 := hdimV.symm.trans hdimV2
    have e2 : (mW' : WithBot ℕ∞) = m := hdimW'.symm.trans hdimW
    have e3 : (mV2 : ℕ∞) = mW' := (hzV2 hzcl).symm.trans (hzW' hzcl)
    have e1' : mV = mV2 := by exact_mod_cast e1
    have e2' : mW' = m := by exact_mod_cast e2
    have e3' : mV2 = mW' := by exact_mod_cast e3
    rw [e1', e3', e2'] at hxle
    exact hxle
  · exact le_iSup_of_le w hw.ge

/-- **`paper-p.tex`, l. 554–555.** For an integral scheme `X` locally of
finite type over a field and a codimension-one point `y`, the reduced closure
`B` of `y` satisfies `dim B + 1 = dim X`: the dimension drops by exactly one
at each step of the recursion in `def:pcfawd`. -/
theorem topologicalKrullDim_pointClosure_add_one_eq
    (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (y : X) (hy : Order.coheight y = 1) :
    topologicalKrullDim (pointClosureIdealSheaf y).subscheme + 1 = topologicalKrullDim X := by
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ (⊤ : X.Opens) from trivial)
  let U : X.affineOpens := ⟨V, hV⟩
  let I := pointClosureIdealSheaf y
  let ι := I.subschemeι
  have hX := topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen k s V hV ⟨y, hyV⟩
  have hWaff : IsAffineOpen (ι ⁻¹ᵁ V) := hV.preimage ι
  have hWne : ((ι ⁻¹ᵁ V : I.subscheme.Opens) : Set I.subscheme).Nonempty := by
    refine ⟨genericPoint I.subscheme, ?_⟩
    change ι (genericPoint I.subscheme) ∈ V
    rw [pointClosureSubscheme_genericPoint]
    exact hyV
  have hB := topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen k (ι ≫ s) (ι ⁻¹ᵁ V)
    hWaff hWne
  have hiso : ringKrullDim Γ(I.subscheme, ι ⁻¹ᵁ V) =
      ringKrullDim (Γ(X, V) ⧸ (hV.primeIdealOf ⟨y, hyV⟩).asIdeal) := by
    rw [← pointClosureIdealSheaf_ideal y U hyV]
    exact ringKrullDim_eq_of_ringEquiv (I.subschemeObjIso U).commRingCatIsoToRingEquiv
  letI := schemeAffineAlgebraOfField k s U
  haveI := schemeAffineAlgebraOfField_finiteType k s U
  haveI : Nonempty V := ⟨⟨y, hyV⟩⟩
  have hht : (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.height = 1 :=
    (affineOpen_primeIdealOf_height hV y hyV).trans hy
  rw [hB, hX, hiso]
  exact ringKrullDim_quotient_add_one_of_height_eq_one k Γ(X, V) _ hht

/-- The recursion of `def:pcfawd` lowers the dimension by exactly one: the
return of `f^p` on `B = f^r(A)`, for an integral effective divisor `A`, lives
on a scheme of dimension `dim X - 1`.

`paper-p.tex` correspondence: Definition 3.3 (`def:pcfawd`). -/
theorem topologicalKrullDim_divisorReturn_add_one_eq
    (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] (C : SchemeDivisorPoint X) (r : ℕ) :
    topologicalKrullDim (pointClosureIdealSheaf (schemePointIterate f r C.1)).subscheme + 1 =
      topologicalKrullDim X := by
  haveI := isFinite_end_pow f r
  haveI := isDominant_end_pow f r
  exact topologicalKrullDim_pointClosure_add_one_eq k s _
    (coheight_apply_eq_one_of_finite_of_locallyOfFiniteType k s (End.of f ^ r).asHom C)

#print axioms topologicalKrullDim_divisorReturn_add_one_eq
#print axioms topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen
#print axioms topologicalKrullDim_pointClosure_add_one_eq

end

end Pcf
