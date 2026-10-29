/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.ClosureStalk
public import Pcf.Bounding.AllCodimChartProof
public import Pcf.Bounding.PaperPBoundingIncidence

/-!
# Transporting the tame chart to the original reduced divisor restriction

The characteristic-independent tame chart gives formal étaleness for the
quotient map of ambient stalks. The canonical equivalences between these
quotients and the stalks of the original reduced point closures identify that
map with the actual restricted scheme morphism. This is the final stalk
comparison needed after the local hypotheses of `thm:bounding` are assembled.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- Formal étaleness of the ambient closure quotient map is exactly formal
étaleness of the stalk map of the original reduced point-closure restriction. -/
theorem pointClosureSubschemeMap_formallyEtale_of_closureStalk
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : X)
    (x : (pointClosureIdealSheaf d).subscheme)
    (h : d ⤳ (pointClosureIdealSheaf d).subschemeι x)
    (hformal : (stalkGenerizationQuotientMap f h).FormallyEtale) :
    ((pointClosureSubschemeMap f d (f d) rfl).stalkMap x).hom.FormallyEtale := by
  let g := pointClosureSubschemeMap f d (f d) rfl
  let eX := pointClosureStalkEquiv d x h
  have hfx : (pointClosureIdealSheaf (f d)).subschemeι (g x) =
      f ((pointClosureIdealSheaf d).subschemeι x) := by
    rw [← Scheme.Hom.comp_apply, pointClosureSubschemeMap_subschemeι,
      Scheme.Hom.comp_apply]
  let eY := pointClosureStalkEquiv' (f d) (g x) hfx (h.map f.continuous)
  have hcomm : eX.toRingHom.comp (stalkGenerizationQuotientMap f h) =
      (g.stalkMap x).hom.comp eY.toRingHom := by
    ext y
    exact (pointClosureStalkEquiv_naturality d f x h y).symm
  have hcomp : (eX.toRingHom.comp (stalkGenerizationQuotientMap f h)).FormallyEtale :=
    formallyEtale_respectsIso.1 _ eX hformal
  have hgcomp : ((g.stalkMap x).hom.comp eY.toRingHom).FormallyEtale :=
    hcomm ▸ hcomp
  have hcancel := formallyEtale_respectsIso.2
    ((g.stalkMap x).hom.comp eY.toRingHom) eY.symm hgcomp
  simpa only [RingHom.comp_assoc, eY.toRingHom_comp_symm_toRingHom,
    RingHom.comp_id] using hcancel

/-- The characteristic-`p` tame chart, applied at a point of the *actual*
original reduced source divisor, gives formal étaleness of the original
restricted morphism. The remaining inputs are precisely the local geometric
conditions to be extracted from avoiding the manuscript's `Σ`. -/
theorem pointClosureSubschemeMap_formallyEtale_of_tameChart
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (s : Y ⟶ Spec (.of k)) (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    (hmono : IsPrimeToPMonodromyMap p f)
    (d : SchemeDivisorPoint X)
    (x : (pointClosureIdealSheaf d.1).subscheme)
    (h : d.1 ⤳ (pointClosureIdealSheaf d.1).subschemeι x)
    (hcoh : Order.coheight ((pointClosureIdealSheaf d.1).subschemeι x) = 2)
    (hprin : (stalkGenerizationPrime Y (h.map f.continuous)).IsPrincipal)
    (hdvr : IsDiscreteValuationRing
      (closureStalk Y (h.map f.continuous)))
    (hunram : ∀ w : SchemeDivisorPoint X,
      f w.1 ⤳ f ((pointClosureIdealSheaf d.1).subschemeι x) →
      f w.1 ≠ f d.1 → (f.stalkMap w.1).hom.FormallyEtale) :
    ((pointClosureSubschemeMap f d.1 (f d.1) rfl).stalkMap x).hom.FormallyEtale := by
  have hchart := allCodimChartPropertyWithFormalEtale p hp k s f hmono d
    ((pointClosureIdealSheaf d.1).subschemeι x) h hcoh hprin hdvr hunram
  exact pointClosureSubschemeMap_formallyEtale_of_closureStalk f d.1 x h hchart.2

/-- Every source divisor above a different target divisor through a point
outside the manuscript's exact `Σ` is already étale for the original finite
normal cover. This discharges the chart's other-branch hypothesis directly
from the weighted branch correction, including inseparable residue extensions. -/
theorem paperPBoundingSigma_otherBranch_formallyEtale
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (B : SchemeDivisorPoint Y)
    (Q : (pointClosureIdealSheaf B.1).subscheme)
    (hQ : Q ∉ paperPBoundingSigma f B)
    (w : SchemeDivisorPoint X)
    (hw : f w.1 ⤳ (pointClosureIdealSheaf B.1).subschemeι Q)
    (hneq : f w.1 ≠ B.1) :
    (f.stalkMap w.1).hom.FormallyEtale := by
  by_contra hnot
  have hdelta1 : schemeDivisorDelta f w ≠ 1 := by
    intro heq
    exact hnot ((schemeDivisorDelta_eq_one_iff_formallyEtale f w).mp heq)
  have hpositive : 0 < schemeDivisorDelta f w :=
    schemeDivisorDelta_pos_of_isFinite f w
  have hdelta : 1 < schemeDivisorDelta f w := by omega
  have hbranch : f w.1 ∈ weightedBranchPointSet f := by
    rw [weightedBranchPointSet_eq_schemeDelta_image_of_normal f]
    exact ⟨w, hdelta, rfl⟩
  have hS : f w.1 ∈ {y | y ∈ weightedBranchPointSet f ∧ y ≠ B.1} :=
    ⟨hbranch, hneq⟩
  have hZ : (pointClosureIdealSheaf B.1).subschemeι Q ∈
      paperPBoundingOtherBranch f B :=
    (closure_mono (Set.singleton_subset_iff.mpr hS))
      (specializes_iff_mem_closure.mp hw)
  apply hQ
  change Q ∈ ((pointClosureIdealSheaf B.1).subschemeι ⁻¹'
      paperPBoundingOtherBranch f B ∪
    (pointClosureIdealSheaf B.1).subschemeι ⁻¹' stalkSingularLocus Y) ∪
      stalkSingularLocus (pointClosureIdealSheaf B.1).subscheme
  exact Or.inl (Or.inl hZ)

/-- At a divisor-generic point of the original reduced target divisor, its
regular stalk is a DVR. The ambient closure quotient has the same DVR
structure, via the canonical point-closure stalk equivalence. -/
theorem paperPBounding_regularDivisor_closureStalk_dvr
    {Y : Scheme.{u}} (B : SchemeDivisorPoint Y)
    (Q : SchemeDivisorPoint (pointClosureIdealSheaf B.1).subscheme)
    (h : B.1 ⤳ (pointClosureIdealSheaf B.1).subschemeι Q.1)
    (hregular : Q.1 ∉ stalkSingularLocus
      (pointClosureIdealSheaf B.1).subscheme) :
    IsDiscreteValuationRing (closureStalk Y h) := by
  let D := (pointClosureIdealSheaf B.1).subscheme
  letI : IsRegularLocalRing (D.presheaf.stalk Q.1) :=
    isRegularLocalRing_stalk_of_notMem_stalkSingularLocus hregular
  have hdim : ringKrullDim (D.presheaf.stalk Q.1) = 1 := by
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight Q.1, Q.2]
    norm_num
  letI : IsDiscreteValuationRing (D.presheaf.stalk Q.1) :=
    isDiscreteValuationRing_of_isRegularLocalRing_of_ringKrullDim_eq_one _ hdim
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (pointClosureStalkEquiv B.1 Q.1 h).symm

/-- At a regular codimension-two ambient point where the reduced divisor is
regular in codimension one, the prime of the divisor is principal in the
actual ambient stalk. This is the local Cartier input of the tame chart. -/
theorem paperPBounding_regularFlag_stalkGenerizationPrime_principal
    {Y : Scheme.{u}} [IsIntegral Y]
    (B : SchemeDivisorPoint Y)
    (Q : SchemeDivisorPoint (pointClosureIdealSheaf B.1).subscheme)
    (h : B.1 ⤳ (pointClosureIdealSheaf B.1).subschemeι Q.1)
    (hcoh : Order.coheight
      ((pointClosureIdealSheaf B.1).subschemeι Q.1) = 2)
    (hambient : (pointClosureIdealSheaf B.1).subschemeι Q.1 ∉
      stalkSingularLocus Y)
    (hdivisor : Q.1 ∉ stalkSingularLocus
      (pointClosureIdealSheaf B.1).subscheme) :
    (stalkGenerizationPrime Y h).IsPrincipal := by
  let E : Y := (pointClosureIdealSheaf B.1).subschemeι Q.1
  let R := Y.presheaf.stalk E
  let P := stalkGenerizationPrime Y h
  letI : IsRegularLocalRing R :=
    isRegularLocalRing_stalk_of_notMem_stalkSingularLocus hambient
  have hdim : ringKrullDim R = 2 := by
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight E, hcoh]
    norm_num
  have hquotreg : IsRegularLocalRing (R ⧸ P) := by
    letI : IsRegularLocalRing
        ((pointClosureIdealSheaf B.1).subscheme.presheaf.stalk Q.1) :=
      isRegularLocalRing_stalk_of_notMem_stalkSingularLocus hdivisor
    exact IsRegularLocalRing.of_ringEquiv
      (pointClosureStalkEquiv B.1 Q.1 h).symm
  have hquotdim : ringKrullDim (R ⧸ P) = 1 := by
    calc
      ringKrullDim (R ⧸ P) =
          ringKrullDim ((pointClosureIdealSheaf B.1).subscheme.presheaf.stalk Q.1) :=
        (pointClosureStalkEquiv B.1 Q.1 h).ringKrullDim
      _ = ↑(Order.coheight Q.1) :=
        AlgebraicGeometry.ringKrullDim_stalk_eq_coheight Q.1
      _ = 1 := by norm_num [Q.2]
  obtain ⟨W, hW, hEW, -⟩ := exists_isAffineOpen_mem_and_subset
    (show E ∈ (⊤ : Y.Opens) from trivial)
  let U : Y.affineOpens := ⟨W, hW⟩
  have hdW : B.1 ∈ W := h.mem_open W.isOpen hEW
  let D : Ideal Γ(Y, W) := (hW.primeIdealOf ⟨B.1, hdW⟩).asIdeal
  let q : Ideal Γ(Y, W) := (hW.primeIdealOf ⟨E, hEW⟩).asIdeal
  letI : Algebra Γ(Y, W) R := Y.presheaf.algebra_section_stalk ⟨E, hEW⟩
  letI : IsLocalization.AtPrime R q := hW.isLocalization_stalk ⟨E, hEW⟩
  have hDq : D ≤ q := affineOpen_primeIdealOf_le_of_specializes hW h hEW
  have hdisj : Disjoint (q.primeCompl : Set Γ(Y, W)) (D : Set Γ(Y, W)) := by
    rw [Set.disjoint_left]
    exact fun r hrq hrD => hrq (hDq hrD)
  have hDheight : D.height = 1 := by
    rw [affineOpen_primeIdealOf_height hW B.1 hdW, B.2]
  have hPheight : P.height = 1 := by
    have hPeq : P = D.map (algebraMap Γ(Y, W) R) :=
      affineOpen_stalkGenerizationPrime_eq_map hW h hEW
    rw [hPeq]
    exact (IsLocalization.height_map_of_disjoint q.primeCompl D hdisj).trans hDheight
  letI : IsRegularLocalRing (R ⧸ P) := hquotreg
  exact heightOne_isPrincipal_of_regularLocalRing_dim_two R hdim P hPheight hquotdim

#print axioms pointClosureSubschemeMap_formallyEtale_of_closureStalk
#print axioms pointClosureSubschemeMap_formallyEtale_of_tameChart
#print axioms paperPBoundingSigma_otherBranch_formallyEtale
#print axioms paperPBounding_regularDivisor_closureStalk_dvr
#print axioms paperPBounding_regularFlag_stalkGenerizationPrime_principal

end
end Pcf
