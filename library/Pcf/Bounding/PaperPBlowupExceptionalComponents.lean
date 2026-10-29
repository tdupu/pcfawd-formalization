/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupArbitraryCentre
public import Mathlib.Topology.KrullDimension

/-!
# Generic points of exceptional components

In `paper-p.tex`, Proposition `prop:bound-blowup`, the selected divisor
`B'` must be an irreducible component of the exceptional inverse image.
On an integral scheme, every codimension-one point in a proper closed
subset is generic for a component of that subset. This applies to the
normalised blow-up's exceptional Cartier support.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

/-- A codimension-one point of a proper closed subset of an integral
scheme is the generic point of an irreducible component of that subset. -/
theorem divisorPoint_irreducibleComponent_of_proper_closed
    {X : Scheme.{u}} [IsIntegral X]
    (E : Set X) (hclosed : IsClosed E) (hproper : E ≠ Set.univ)
    (D : SchemeDivisorPoint X) (hD : D.1 ∈ E) :
    closure ({(⟨D.1, hD⟩ : E)} : Set E) ∈ irreducibleComponents E := by
  letI : LE E := (specializationOrder E).toLE
  letI : Preorder E := (specializationOrder E).toPreorder
  letI : PartialOrder E := specializationOrder E
  letI : QuasiSober E := hclosed.isClosedEmbedding_subtypeVal.quasiSober
  let e : E := ⟨D.1, hD⟩
  have hclosure : closure E ≠ Set.univ := by
    simpa only [hclosed.closure_eq] using hproper
  obtain ⟨z, hz, heq⟩ :=
    QuasiSober.coheight_eq_zero_subset_of_coheight_eq_one
      (p := E) hclosure ⟨hD, D.2⟩
  have hz0 : Order.coheight z = 0 := by
    have hz' := hz
    simp only [Set.mem_ofPred_eq] at hz'
    rw [← specializationPreorder_subtype] at hz'
    exact hz'
  have hze : z = e := Subtype.ext heq
  have he0 : Order.coheight e = 0 := hze ▸ hz0
  let C : IrreducibleCloseds E :=
    (irreducibleSetEquivPoints (α := E)).symm e
  have hCmax : IsMax C := by
    apply ((irreducibleSetEquivPoints (α := E)).isMax_apply).mp
    change IsMax ((irreducibleSetEquivPoints (α := E))
      ((irreducibleSetEquivPoints (α := E)).symm e))
    simpa only [OrderIso.apply_symm_apply] using (Order.coheight_eq_zero.mp he0)
  have hC : (C : Set E) ∈ irreducibleComponents E := by
    rw [irreducibleComponents_eq_maximals_closed]
    refine ⟨⟨C.isClosed, C.isIrreducible⟩, ?_⟩
    intro S hS hCS
    exact hCmax (show C ≤ (⟨S, hS.2, hS.1⟩ : IrreducibleCloseds E) from hCS)
  have hcarrier : (C : Set E) = closure {e} := rfl
  rw [hcarrier] at hC
  exact hC

/-- The normalized exceptional support of a nonzero affine blow-up
centre is a proper closed subset: its generic point maps to the generic
point of the affine base, which is not in the centre. -/
theorem normalizedReesExceptional_support_proper
    {R : Type u} [CommRing R] [IsDomain R]
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    ((normalizedReesExceptionalIdealSheaf I a ha).support :
      Set (Palomar.normalization (reesProj I))) ≠ Set.univ := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let β := normalizedReesProjToSpec I a ha
  letI : IsDominant β := normalizedReesProjToSpec_isDominant I a ha
  intro htop
  have hη : (genericPoint (Palomar.normalization (reesProj I))) ∈
      ((normalizedReesExceptionalIdealSheaf I a ha).support :
        Set (Palomar.normalization (reesProj I))) := by
    rw [htop]
    trivial
  rw [normalizedReesExceptionalIdealSheaf_support] at hη
  change β (genericPoint (Palomar.normalization (reesProj I))) ∈
    PrimeSpectrum.zeroLocus (I : Set R) at hη
  rw [map_genericPoint_eq_of_isDominant β,
    genericPoint_eq_bot_of_affine (CommRingCat.of R)] at hη
  have hle : I ≤ (⊥ : Ideal R) :=
    (PrimeSpectrum.mem_zeroLocus _ (I : Set R)).mp hη
  exact ha (by
    have hm : (a : R) ∈ (⊥ : Ideal R) := hle a.property
    simpa only [Ideal.mem_bot] using hm)

/-- Each codimension-one point of the normalized exceptional support is
its own irreducible component generic point. In particular the divisor
`B'` selected by the blow-up construction is maximal among components
of the exceptional inverse image, as in `prop:bound-blowup`. -/
theorem normalizedReesExceptional_divisor_is_component
    {R : Type u} [CommRing R] [IsDomain R]
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0)
    (D : letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
      SchemeDivisorPoint (Palomar.normalization (reesProj I))) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let E : Set (Palomar.normalization (reesProj I)) :=
      (normalizedReesExceptionalIdealSheaf I a ha).support
    ∀ hD : D.1 ∈ E,
      closure ({(⟨D.1, hD⟩ : E)} : Set E) ∈ irreducibleComponents E := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let E : Set (Palomar.normalization (reesProj I)) :=
    (normalizedReesExceptionalIdealSheaf I a ha).support
  dsimp only
  intro hD
  exact divisorPoint_irreducibleComponent_of_proper_closed
    E (normalizedReesExceptionalIdealSheaf I a ha).support.isClosed
      (normalizedReesExceptional_support_proper I a ha) D hD

#print axioms divisorPoint_irreducibleComponent_of_proper_closed
#print axioms normalizedReesExceptional_support_proper
#print axioms normalizedReesExceptional_divisor_is_component

end
end Pcf.Bounding.AllCodimBlowup
