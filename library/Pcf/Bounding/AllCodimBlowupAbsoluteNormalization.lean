/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupDegreeOneCover
public import Pcf.Bounding.GlobalNormalizationFinite
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Absolute normalization of a Rees blow-up

For a finitely generated center in an integral finite-type algebra over a
field, we build the geometric properties needed to apply the existing
finiteness theorem for absolute normalization. The zero ideal is excluded:
its Rees Proj is empty.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory

universe u

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency.types false

variable {k R : Type u} [Field k] [CommRing R] [IsDomain R]
  [Algebra k R] [Algebra.FiniteType k R]

omit [IsDomain R] in
/-- The Rees algebra of a finitely generated ideal is a finite-type
algebra over the base field. -/
theorem reesAlgebra_finiteType_over_field (I : Ideal R) (hI : I.FG) :
    Algebra.FiniteType k (reesAlgebra I) := by
  haveI : Algebra.FiniteType R (reesAlgebra I) :=
    ⟨(reesAlgebra I).fg_top.mpr (reesAlgebra.fg hI)⟩
  exact Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k R)
    (inferInstance : Algebra.FiniteType R (reesAlgebra I))

omit [IsDomain R] in
/-- Each standard affine chart of the Rees blow-up is a finite-type
algebra over the base field. -/
theorem affineBlowupChart_finiteType_over_field (I : Ideal R)
    (hI : I.FG) (a : I) :
    Algebra.FiniteType k (affineBlowupChart I a) := by
  letI : Algebra.FiniteType k (reesAlgebra I) :=
    reesAlgebra_finiteType_over_field I hI
  exact Algebra.FiniteType.of_surjective
    ((reesChartEval I a).rangeRestrict.restrictScalars k)
    (AlgHom.rangeRestrict_surjective _)

/-- A standard blow-up chart with nonzero denominator is a domain. -/
theorem affineBlowupChart_isDomain_of_nonzero (I : Ideal R) (a : I)
    (ha : (a : R) ≠ 0) : IsDomain (affineBlowupChart I a) := by
  haveI : IsDomain (Localization.Away (a : R)) := Localization.Away.isDomain ha
  infer_instance

/-- Every affine Rees chart is reduced, including the empty charts
corresponding to zero denominators. -/
theorem affineBlowupChart_isReduced (I : Ideal R) (a : I) :
    IsReduced (affineBlowupChart I a) := by
  haveI : IsReduced (Localization.Away (a : R)) := inferInstance
  infer_instance

variable (k)

omit [IsDomain R] in
/-- The degree-zero `Proj` chart is finite type over the field through
its proved identification with the explicit Rees chart. -/
theorem reesProjChart_finiteType_over_field (I : Ideal R)
    (hI : I.FG) (a : I) :
    letI : Algebra k (reesProjChart I a) :=
      ((reesProjChartEquiv I a).symm.toRingHom.comp
        (algebraMap k (affineBlowupChart I a))).toAlgebra
    Algebra.FiniteType k (reesProjChart I a) := by
  letI : Algebra k (reesProjChart I a) :=
    ((reesProjChartEquiv I a).symm.toRingHom.comp
      (algebraMap k (affineBlowupChart I a))).toAlgebra
  exact (affineBlowupChart_finiteType_over_field I hI a).equiv
    (AlgEquiv.ofRingEquiv (f := (reesProjChartEquiv I a).symm) (by intro r; rfl))

omit [IsDomain R] in
/-- The Rees algebra is finite type over its degree-zero part when the
center is finitely generated. -/
theorem reesAlgebra_finiteType_over_zeroGrade (I : Ideal R) (hI : I.FG) :
    Algebra.FiniteType (reesGrade I 0) (reesAlgebra I) := by
  have hFT : Algebra.FiniteType R (reesAlgebra I) :=
    ⟨(reesAlgebra I).fg_top.mpr (reesAlgebra.fg hI)⟩
  obtain ⟨s, hs⟩ := hFT.out
  refine ⟨⟨s, eq_top_iff.mpr ?_⟩⟩
  intro x _
  have hx : x ∈ Algebra.adjoin R (s : Set (reesAlgebra I)) := by
    rw [hs]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap r =>
      convert (Algebra.adjoin (reesGrade I 0)
        (s : Set (reesAlgebra I))).algebraMap_mem (reesGradeZeroMap I r) using 1
      rfl
  | add x y hx hy ihx ihy => exact add_mem (ihx trivial) (ihy trivial)
  | mul x y hx hy ihx ihy => exact mul_mem (ihx trivial) (ihy trivial)

omit [IsDomain R] in
/-- The degree-zero Rees ring consists exactly of constant coefficients. -/
theorem reesGradeZeroMap_surjective (I : Ideal R) :
    Function.Surjective (reesGradeZeroMap I) := by
  intro x
  refine ⟨x.1.1.coeff 0, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact (reesGrade_eq_monomial I 0 x.1 x.2).symm

/-- The blow-up's structural map to the base field. -/
noncomputable def reesProjToSpecField (I : Ideal R) :
    reesProj I ⟶ Spec (.of k) :=
  reesProjToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))

omit [IsDomain R] in
/-- A Rees blow-up of a finitely generated center in an affine finite-type
field scheme is locally of finite type over that field. -/
theorem reesProjToSpecField_locallyOfFiniteType (I : Ideal R) (hI : I.FG) :
    LocallyOfFiniteType (reesProjToSpecField (k := k) I) := by
  haveI : Algebra.FiniteType (reesGrade I 0) (reesAlgebra I) :=
    reesAlgebra_finiteType_over_zeroGrade I hI
  haveI : LocallyOfFiniteType (Proj.toSpecZero (reesGrade I)) := inferInstance
  let φ : CommRingCat.of R ⟶ CommRingCat.of (reesGrade I 0) :=
    CommRingCat.ofHom (reesGradeZeroMap I)
  haveI : IsClosedImmersion (Spec.map φ) := by
    apply IsClosedImmersion.spec_of_surjective
    exact reesGradeZeroMap_surjective I
  haveI : LocallyOfFiniteType
      (Spec.map φ) := inferInstance
  haveI : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  unfold reesProjToSpecField reesProjToSpec reesProj
  infer_instance

/-- A nonzero blow-up center gives a relevant zero homogeneous prime,
which is the generic point of the Rees Proj. -/
theorem reesProj_irreducibleSpace (I : Ideal R) (a : I)
    (ha : (a : R) ≠ 0) : IrreducibleSpace (reesProj I) := by
  haveI : IsDomain (reesAlgebra I) := inferInstance
  let η : reesProj I :=
    { asHomogeneousIdeal := ⊥
      isPrime := by
        change (⊥ : Ideal (reesAlgebra I)).IsPrime
        infer_instance
      not_irrelevant_le := by
        intro h
        have hmem : reesDegreeOne I a ∈
            HomogeneousIdeal.irrelevant (reesGrade I) :=
          HomogeneousIdeal.mem_irrelevant_of_mem (reesGrade I) (by decide)
            (reesDegreeOne_mem_grade I a)
        have hzero : reesDegreeOne I a = 0 := by
          exact (Submodule.mem_bot _).mp (h hmem)
        have hcoeff := congrArg (fun P : reesAlgebra I => P.1.coeff 1) hzero
        exact ha (by simpa [reesDegreeOne] using hcoeff)
    }
  have hη : closure ({η} : Set (reesProj I)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact (ProjectiveSpectrum.le_iff_mem_closure (reesGrade I) η x).mp (by
      change (⊥ : HomogeneousIdeal (reesGrade I)) ≤ x.asHomogeneousIdeal
      exact bot_le)
  exact (irreducibleSpace_def (reesProj I)).mpr (by
    change IsIrreducible (Set.univ : Set (reesProj I))
    rw [← hη]
    exact isIrreducible_singleton.closure)

/-- The degree-one affine cover consists of reduced chart schemes, hence
the Rees blow-up is reduced. -/
theorem reesProj_isReduced (I : Ideal R) : IsReduced (reesProj I) := by
  let 𝒰 := reesProjDegreeOneCover I
  haveI (a : I) : _root_.IsReduced (reesProjChart I a) := by
    haveI : _root_.IsReduced (affineBlowupChart I a) :=
      affineBlowupChart_isReduced I a
    exact isReduced_of_injective (reesProjChartEquiv I a)
      (reesProjChartEquiv I a).injective
  haveI (a : 𝒰.openCover.I₀) : IsReduced (𝒰.openCover.X a) := by
    change IsReduced (Spec (.of (reesProjChart I a)))
    infer_instance
  exact IsReduced.of_openCover (reesProj I) 𝒰.openCover

/-- For a nonzero center, the actual Rees Proj blow-up is an integral
scheme. -/
theorem reesProj_isIntegral (I : Ideal R) (a : I)
    (ha : (a : R) ≠ 0) : IsIntegral (reesProj I) := by
  letI : IrreducibleSpace (reesProj I) := reesProj_irreducibleSpace I a ha
  letI : IsReduced (reesProj I) := reesProj_isReduced I
  exact isIntegral_of_irreducibleSpace_of_isReduced _

include k in
/-- The absolute normalization of a Rees blow-up of a nonzero finitely
generated ideal in an integral finite-type field algebra is finite. -/
theorem reesProj_absoluteNormalizationMap_isFinite (I : Ideal R)
    (hI : I.FG) (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    IsFinite (Palomar.normalizationMap (reesProj I)) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  letI : LocallyOfFiniteType (reesProjToSpecField (k := k) I) :=
    reesProjToSpecField_locallyOfFiniteType k I hI
  exact Pcf.schemeGlobalNormalizationMap_isFinite (reesProj I) k
    (reesProjToSpecField k I)

#print axioms reesAlgebra_finiteType_over_field
#print axioms affineBlowupChart_finiteType_over_field
#print axioms affineBlowupChart_isDomain_of_nonzero
#print axioms affineBlowupChart_isReduced
#print axioms reesProjChart_finiteType_over_field
#print axioms reesAlgebra_finiteType_over_zeroGrade
#print axioms reesGradeZeroMap_surjective
#print axioms reesProjToSpecField_locallyOfFiniteType
#print axioms reesProj_irreducibleSpace
#print axioms reesProj_isReduced
#print axioms reesProj_isIntegral
#print axioms reesProj_absoluteNormalizationMap_isFinite

end Pcf.Bounding.AllCodimBlowup
