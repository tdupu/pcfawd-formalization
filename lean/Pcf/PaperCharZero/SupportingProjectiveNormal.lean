/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingProjectiveGeometry
public import Pcf.Bounding.NormalSchemePCFComparison
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Normality of the actual projective scheme
-/

@[expose] public section
namespace Pcf.PaperCharZero
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "polyGrade" => MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K

/-- The reindexed standard polynomial coordinate chart has its expected
projective basic open as image. -/
theorem projAnyTargetChartToProj_opensRange
    (e : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    (projAnyTargetChartToProj (K := K) e).opensRange =
      AlgebraicGeometry.Proj.basicOpen polyGrade (X (e.symm (Sum.inr ()))) := by
  unfold projAnyTargetChartToProj
  have : IsIso (CommRingCat.ofHom (projAnyTargetChartRingEquiv (K := K) e).toRingHom) :=
    inferInstanceAs (IsIso (projAnyTargetChartRingEquiv (K := K) e).toCommRingCatIso.hom)
  rw [Scheme.Hom.opensRange_comp_of_isIso, AlgebraicGeometry.Proj.opensRange_awayι]

/-- The standard `n + 1` projective opens are covered by ordinary affine
`n`-space, in the form of an actual scheme open cover.

Divergence from Stacks Lemma 27.13.3: this is the field-base analogue of
the statement over `ℤ`; the chart images are identified by
`projAnyTargetChartToProj_opensRange`. -/
@[stacks 01NG "standard affine coordinate cover, over a field"]
noncomputable def projProjectiveCoordinateOpenCover :
    (AlgebraicGeometry.Proj polyGrade).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin n ⊕ Unit)
    (fun _ => Spec (CommRingCat.of (MvPolynomial (Fin n) K)))
    (fun b => projAnyTargetChartToProj (Equiv.swap b (Sum.inr ()))) (by
      intro x
      classical
      obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp
        ((projSourceCoordinates_basicOpen_cover (K := K) (n := n)).ge (Set.mem_univ x))
      have hx : x ∈ (projAnyTargetChartToProj (K := K)
          (Equiv.swap b (Sum.inr ()))).opensRange := by
        rw [projAnyTargetChartToProj_opensRange]
        simpa using hb
      obtain ⟨p, hp⟩ := hx
      exact ⟨b, p, hp⟩)

/-- The finite standard affine cover makes the actual projective scheme
Noetherian, including quasi-compactness. -/
instance projProjective_isNoetherian : IsNoetherian (AlgebraicGeometry.Proj polyGrade) := by
  let U := projProjectiveCoordinateOpenCover (K := K) (n := n)
  have : Finite U.I₀ := by change Finite (Fin n ⊕ Unit); infer_instance
  have (b : U.I₀) : IsAffine (U.X b) := by change IsAffine (Spec _); infer_instance
  apply (isNoetherian_iff_of_finite_affine_openCover
    (𝒰 := U)).mpr
  intro b
  change IsNoetherianRing Γ(Spec (CommRingCat.of (MvPolynomial (Fin n) K)), ⊤)
  exact isNoetherianRing_of_ringEquiv _
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) K))).symm.commRingCatIsoToRingEquiv

/-- Every projective local ring has characteristic zero when the base
field does, by transport through a standard polynomial chart. -/
theorem projProjective_stalk_charZero [CharZero K]
    (x : AlgebraicGeometry.Proj polyGrade) :
    CharZero ((AlgebraicGeometry.Proj polyGrade).presheaf.stalk x) := by
  let U := projProjectiveCoordinateOpenCover (K := K) (n := n)
  obtain ⟨b, p, rfl⟩ := U.exists_eq x
  have : CharZero ((U.X b).presheaf.stalk p) := by
    change CharZero ((Spec (CommRingCat.of (MvPolynomial (Fin n) K))).presheaf.stalk p)
    have : CharZero (Localization.AtPrime p.asIdeal) :=
      charZero_of_injective_ringHom
        (IsLocalization.injective (Localization.AtPrime p.asIdeal)
          p.asIdeal.primeCompl_le_nonZeroDivisors)
    exact charZero_of_injective_ringHom
      (Spec.stalkIso
        (CommRingCat.of (MvPolynomial (Fin n) K)) p).symm.commRingCatIsoToRingEquiv.injective
  exact charZero_of_injective_ringHom
    (asIso ((U.f b).stalkMap p)).symm.commRingCatIsoToRingEquiv.injective

/-- Each actual projective local ring is integrally closed, using its
open immersion from an ordinary polynomial coordinate chart. -/
theorem projProjective_stalk_integrallyClosed
    (x : AlgebraicGeometry.Proj polyGrade) :
    IsIntegrallyClosed ((AlgebraicGeometry.Proj polyGrade).presheaf.stalk x) := by
  let U := projProjectiveCoordinateOpenCover (K := K) (n := n)
  obtain ⟨b, p, rfl⟩ := U.exists_eq x
  have : IsIntegrallyClosed ((U.X b).presheaf.stalk p) := by
    change IsIntegrallyClosed ((Spec (CommRingCat.of (MvPolynomial (Fin n) K))).presheaf.stalk p)
    have : IsIntegrallyClosed (Localization.AtPrime p.asIdeal) :=
      isIntegrallyClosed_of_isLocalization _ _ p.asIdeal.primeCompl_le_nonZeroDivisors
    exact IsIntegrallyClosed.of_equiv
      (Spec.stalkIso (CommRingCat.of (MvPolynomial (Fin n) K)) p).symm.commRingCatIsoToRingEquiv
  exact IsIntegrallyClosed.of_equiv (asIso ((U.f b).stalkMap p)).symm.commRingCatIsoToRingEquiv

/-- Every actual affine coordinate ring of projective space is integrally
closed, so projective space is normal in the divisor dictionary's sense. -/
instance projProjective_isNormalScheme : IsNormalScheme (AlgebraicGeometry.Proj polyGrade) := by
  constructor
  intro U
  classical
  by_cases hU : Nonempty (U : (AlgebraicGeometry.Proj polyGrade).Opens)
  · let := hU
    apply IsIntegrallyClosed.of_localization_maximal
    intro P _ _
    let p : PrimeSpectrum Γ(AlgebraicGeometry.Proj polyGrade, U) := ⟨P, inferInstance⟩
    have : IsIntegrallyClosed ((AlgebraicGeometry.Proj polyGrade).presheaf.stalk
        (U.2.fromSpec p)) := projProjective_stalk_integrallyClosed _
    have : IsIntegrallyClosed
        ((Spec (CommRingCat.of Γ(AlgebraicGeometry.Proj polyGrade, U))).presheaf.stalk p) :=
      IsIntegrallyClosed.of_equiv (asIso (U.2.fromSpec.stalkMap p)).commRingCatIsoToRingEquiv
    exact IsIntegrallyClosed.of_equiv
      (Spec.stalkIso
        (CommRingCat.of Γ(AlgebraicGeometry.Proj polyGrade, U)) p).commRingCatIsoToRingEquiv
  · have hbot : (U : (AlgebraicGeometry.Proj polyGrade).Opens) = ⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      exact (hU ⟨⟨x, hx⟩⟩).elim
    have : Subsingleton Γ(AlgebraicGeometry.Proj polyGrade, U) := by rw [hbot]; infer_instance
    have : Subsingleton (FractionRing Γ(AlgebraicGeometry.Proj polyGrade, U)) :=
      Algebra.subsingleton Γ(AlgebraicGeometry.Proj polyGrade, U) _
    constructor
    · exact Function.injective_of_subsingleton _
    · intro x
      constructor
      · intro _
        exact ⟨0, Subsingleton.elim _ _⟩
      · rintro ⟨y, rfl⟩
        exact isIntegral_algebraMap

#print axioms projAnyTargetChartToProj_opensRange
#print axioms projProjectiveCoordinateOpenCover
#print axioms projProjective_isNoetherian
#print axioms projProjective_stalk_charZero
#print axioms projProjective_stalk_integrallyClosed
#print axioms projProjective_isNormalScheme
end Pcf.PaperCharZero
