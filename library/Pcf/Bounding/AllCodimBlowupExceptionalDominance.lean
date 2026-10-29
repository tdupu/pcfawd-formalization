/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupExceptionalSurjectivity

/-!
# An exceptional component dominates an integral blow-up centre

The normalized exceptional support has finitely many components and covers
an integral centre. The normalized blow-up is proper over the base, so the
images of those components are closed. Irreducibility of the centre then
forces one component to have the entire centre as image. This is the
existence of a `D_j` in `paper-p.tex`, Theorem `thm:allcodim-normal`.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

variable {k R : Type u} [Field k] [CommRing R] [IsDomain R]
  [Algebra k R] [Algebra.FiniteType k R]

/-- At least one irreducible component of the normalized exceptional
support maps onto the whole integral closed centre. -/
theorem exists_normalizedReesExceptional_component_dominating_center
    (k : Type u) [Field k] [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) [I.IsPrime] (hI : I.FG)
    (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let E : Set (Palomar.normalization (reesProj I)) :=
      (normalizedReesExceptionalIdealSheaf I a ha).support
    let q : Palomar.normalization (reesProj I) ⟶ Spec (.of R) :=
      Palomar.normalizationMap (reesProj I) ≫ reesProjToSpec I
    ∃ C ∈ irreducibleComponents E,
      (fun x : E => q x.1) '' C = PrimeSpectrum.zeroLocus (I : Set R) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let E : Set (Palomar.normalization (reesProj I)) :=
    (normalizedReesExceptionalIdealSheaf I a ha).support
  let q : Palomar.normalization (reesProj I) ⟶ Spec (.of R) :=
    Palomar.normalizationMap (reesProj I) ≫ reesProjToSpec I
  let qE : E → Spec (.of R) := fun x => q x.1
  letI : NoetherianSpace (Palomar.normalization (reesProj I)) :=
    normalizedReesProj_noetherianSpace k I hI a ha
  have hfinite : (irreducibleComponents E).Finite :=
    normalizedReesExceptional_finite_components k I hI a ha
  letI : IsFinite (Palomar.normalizationMap (reesProj I)) :=
    reesProj_absoluteNormalizationMap_isFinite k I hI a ha
  letI : IsProper (reesProjToSpec I) := reesProjToSpec_isProper I hI
  haveI : IsProper q := by
    dsimp [q]
    infer_instance
  have hEclosed : IsClosed E :=
    (normalizedReesExceptionalIdealSheaf I a ha).support.isClosed
  have hclosed : IsClosedMap qE :=
    q.isClosedMap.comp hEclosed.isClosedMap_subtype_val
  let S : Set (Set (Spec (.of R))) :=
    (fun C : Set E => qE '' C) '' irreducibleComponents E
  have hSfinite : S.Finite := hfinite.image _
  have hSclosed : ∀ Z ∈ S, IsClosed Z := by
    intro Z hZ
    obtain ⟨C, hC, rfl⟩ := hZ
    exact hclosed C (isClosed_of_mem_irreducibleComponents C hC)
  have hcover : PrimeSpectrum.zeroLocus (I : Set R) ⊆ ⋃₀ S := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ :=
      normalizedReesExceptional_support_surjective_to_center k I hI a ha hy
    let xe : E := ⟨x, hx⟩
    have hxe : xe ∈ ⋃₀ irreducibleComponents E := by
      rw [sUnion_irreducibleComponents]
      trivial
    obtain ⟨C, hC, hxC⟩ := hxe
    have hyC : y ∈ qE '' C := ⟨xe, hxC, hxy⟩
    have hCS : qE '' C ∈ S := ⟨C, hC, rfl⟩
    exact Set.mem_sUnion_of_mem hyC hCS
  have hirr : IsIrreducible (PrimeSpectrum.zeroLocus (I : Set R)) :=
    (PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical I
      (Ideal.IsPrime.isRadical (inferInstance : I.IsPrime))).mpr inferInstance
  obtain ⟨Z, hZ, hsub⟩ := isIrreducible_iff_sUnion_isClosed.mp hirr
    hSfinite.toFinset (by
      intro Z hZ
      exact hSclosed Z (hSfinite.mem_toFinset.mp hZ))
    (by
      change PrimeSpectrum.zeroLocus (I : Set R) ⊆
        ⋃₀ (hSfinite.toFinset : Set (Set (Spec (.of R))))
      rw [hSfinite.coe_toFinset]
      exact hcover)
  obtain ⟨C, hC, rfl⟩ : Z ∈ S := hSfinite.mem_toFinset.mp hZ
  refine ⟨C, hC, Set.Subset.antisymm ?_ hsub⟩
  intro y hy
  obtain ⟨x, -, rfl⟩ := hy
  exact (Set.ext_iff.mp
    (normalizedReesExceptionalIdealSheaf_support I a ha) x.1).mp x.2

#print axioms exists_normalizedReesExceptional_component_dominating_center

end
end Pcf.Bounding.AllCodimBlowup
