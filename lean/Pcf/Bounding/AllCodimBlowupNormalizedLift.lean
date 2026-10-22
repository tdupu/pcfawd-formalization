/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupAbsoluteNormalization
public import Pcf.Bounding.AllCodimBlowupFiniteLift
public import Pcf.Bounding.GlobalNormalizationMorphism

/-!
# The finite map between absolute normalizations of Rees blow-ups

An injective finite map of integral affine varieties induces a dominant finite
map of their Rees blow-ups.  Its normalization lift is finite and commutes with
the original blow-up map.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

set_option linter.style.haveILetI false

noncomputable section

variable {R S : Type u} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]

/-- The zero homogeneous prime is the generic point of a nonzero Rees Proj. -/
private def reesGenericPoint (I : Ideal R) (a : I) (ha : (a : R) ≠ 0) : reesProj I :=
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
      have hzero : reesDegreeOne I a = 0 :=
        (Submodule.mem_bot _).mp (h hmem)
      have hcoeff := congrArg (fun P : reesAlgebra I => P.1.coeff 1) hzero
      exact ha (by simpa [reesDegreeOne] using hcoeff) }

private theorem reesGenericPoint_dense (I : Ideal R) (a : I) (ha : (a : R) ≠ 0) :
    closure ({reesGenericPoint I a ha} : Set (reesProj I)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact (ProjectiveSpectrum.le_iff_mem_closure (reesGrade I)
    (reesGenericPoint I a ha) x).mp (by
      change (⊥ : HomogeneousIdeal (reesGrade I)) ≤ x.asHomogeneousIdeal
      exact bot_le)

/-- The Rees Proj map of an injective coefficient map is dominant when the
center contains a nonzero element. -/
theorem reesProjMap_isDominant_of_injective (f : R →+* S)
    (hf : Function.Injective f) (I : Ideal R) (a : I) (ha : (a : R) ≠ 0) :
    IsDominant (reesProjMap f I) := by
  let b : I.map f := mappedCenterElement f I a
  have hb : (b : S) ≠ 0 := fun h => ha (hf (by simpa [b, mappedCenterElement] using h))
  let ηS := reesGenericPoint (I.map f) b hb
  let ηR := reesGenericPoint I a ha
  have hmap : reesProjMap f I ηS = ηR := by
    change ProjectiveSpectrum.comapFun (gradedReesMap f I)
      (gradedReesMap_irrelevant_le f I) ηS = ηR
    apply ProjectiveSpectrum.ext
    change (⊥ : HomogeneousIdeal (reesGrade (I.map f))).comap
      (gradedReesMap f I) = ⊥
    exact HomogeneousIdeal.ext
      (Ideal.comap_bot_of_injective (gradedReesMap f I)
        (reesAlgebraMap_injective f hf I))
  rw [isDominant_iff, denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ closure ({ηR} : Set (reesProj I)) := by
    rw [show ηR = reesGenericPoint I a ha from rfl,
      reesGenericPoint_dense I a ha]
    trivial
  apply (closure_mono (show ({ηR} : Set (reesProj I)) ⊆
      Set.range (reesProjMap f I) from by
        intro y hy
        rcases Set.mem_singleton_iff.mp hy with rfl
        exact ⟨ηS, hmap⟩)) hx

/-- The actual map between the absolute normalizations of two Rees blow-ups
associated to an injective finite ring map. -/
def normalizedReesProjMap (f : R →+* S) (hf : Function.Injective f)
    (hfin : f.Finite) (I : Ideal R) (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let b : I.map f := mappedCenterElement f I a
    letI : IsIntegral (reesProj (I.map f)) :=
      reesProj_isIntegral (I.map f) b
        (fun h => ha (hf (by simpa [b, mappedCenterElement] using h)))
    Palomar.normalization (reesProj (I.map f)) ⟶ Palomar.normalization (reesProj I) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let b : I.map f := mappedCenterElement f I a
  have hb : (b : S) ≠ 0 := fun h => ha (hf (by simpa [b, mappedCenterElement] using h))
  letI : IsIntegral (reesProj (I.map f)) := reesProj_isIntegral (I.map f) b hb
  letI : IsFinite (reesProjMap f I) := reesProjMap_isFinite f I hfin
  letI : IsDominant (reesProjMap f I) :=
    reesProjMap_isDominant_of_injective f hf I a ha
  exact Pcf.schemeGlobalNormalizationMorphism (reesProjMap f I)

/-- The lift commutes with the finite Rees blow-up map and the absolute
normalization maps. -/
theorem normalizedReesProjMap_comm (f : R →+* S) (hf : Function.Injective f)
    (hfin : f.Finite) (I : Ideal R) (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let b : I.map f := mappedCenterElement f I a
    letI : IsIntegral (reesProj (I.map f)) :=
      reesProj_isIntegral (I.map f) b
        (fun h => ha (hf (by simpa [b, mappedCenterElement] using h)))
    normalizedReesProjMap f hf hfin I a ha ≫ Palomar.normalizationMap (reesProj I) =
      Palomar.normalizationMap (reesProj (I.map f)) ≫ reesProjMap f I := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let b : I.map f := mappedCenterElement f I a
  have hb : (b : S) ≠ 0 := fun h => ha (hf (by simpa [b, mappedCenterElement] using h))
  letI : IsIntegral (reesProj (I.map f)) := reesProj_isIntegral (I.map f) b hb
  letI : IsFinite (reesProjMap f I) := reesProjMap_isFinite f I hfin
  letI : IsDominant (reesProjMap f I) :=
    reesProjMap_isDominant_of_injective f hf I a ha
  exact Pcf.schemeGlobalNormalizationMorphism_comp (reesProjMap f I)

/-- For finite-type affine varieties over a field, the lifted map between
absolute normalizations of their Rees blow-ups is finite. -/
theorem normalizedReesProjMap_isFinite (k : Type u) [Field k]
    [Algebra k R] [Algebra.FiniteType k R]
    (f : R →+* S) (hf : Function.Injective f)
    (hfin : f.Finite) (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let b : I.map f := mappedCenterElement f I a
    letI : IsIntegral (reesProj (I.map f)) :=
      reesProj_isIntegral (I.map f) b
        (fun h => ha (hf (by simpa [b, mappedCenterElement] using h)))
    IsFinite (normalizedReesProjMap f hf hfin I a ha) := by
  letI : Algebra k S := (f.comp (algebraMap k R)).toAlgebra
  have hFT : (f.comp (algebraMap k R)).FiniteType :=
    hfin.to_finiteType.comp (RingHom.finiteType_algebraMap.mpr inferInstance)
  letI : Algebra.FiniteType k S := RingHom.finiteType_algebraMap.mp hFT
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let b : I.map f := mappedCenterElement f I a
  have hb : (b : S) ≠ 0 := fun h => ha (hf (by simpa [b, mappedCenterElement] using h))
  letI : IsIntegral (reesProj (I.map f)) := reesProj_isIntegral (I.map f) b hb
  letI : IsFinite (reesProjMap f I) := reesProjMap_isFinite f I hfin
  letI : IsDominant (reesProjMap f I) :=
    reesProjMap_isDominant_of_injective f hf I a ha
  have hmap : IsFinite (Palomar.normalizationMap (reesProj (I.map f))) :=
    reesProj_absoluteNormalizationMap_isFinite (k := k) (I.map f)
      (Ideal.FG.map hI f) b hb
  letI : IsFinite (Palomar.normalizationMap (reesProj (I.map f))) := hmap
  exact Pcf.schemeGlobalNormalizationMorphism_isFinite (reesProjMap f I)

#print axioms reesProjMap_isDominant_of_injective
#print axioms normalizedReesProjMap
#print axioms normalizedReesProjMap_comm
#print axioms normalizedReesProjMap_isFinite

end

end Pcf.Bounding.AllCodimBlowup
