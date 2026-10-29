/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Henselian
public import Pcf.Stacks.Abhyankar.StrictHenselization
public import Pcf.Stacks.Abhyankar.StrictHenselizationResidue
public import Pcf.Stacks.Abhyankar.StrictHenselizationStages

/-!
# Henselianity of the pointed-etale local colimit

This file proves the remaining intrinsic clause of strict henselianity.  A monic polynomial over
the local colimit has only finitely many coefficients, so it descends to one pointed etale stage.
A simple root in the residue field gives a point on the standard etale root algebra.  Adding that
pointed etale neighbourhood to the filtered diagram produces the required root back in the local
colimit.
-/

@[expose] public section

open CategoryTheory Polynomial

universe u

namespace Pcf.Stacks.PointedEtaleNeighborhood

variable {R Ω : Type u} [CommRing R] [IsLocalRing R] [Field Ω]
  [Algebra R Ω] [Algebra (IsLocalRing.ResidueField R) Ω]
  [IsScalarTower R (IsLocalRing.ResidueField R) Ω]
  [IsSepClosure (IsLocalRing.ResidueField R) Ω]

/-- The residue-field equivalence sends the residue of an element from a pointed etale stage to
the value of that element at the chosen geometric point. -/
theorem residueFieldAlgEquiv_residue_toLocalColimitAlgHom
    (X : PointedEtaleNeighborhood R Ω) (x : X) :
    residueFieldAlgEquiv (R := R) (Ω := Ω)
        (IsLocalRing.residue (LocalColimit R Ω)
          (toLocalColimitAlgHom (R := R) (Ω := Ω) X x)) =
      X.point x := by
  change residuePoint (R := R) (Ω := Ω) (Field.toIsField Ω)
      (algebraMap (Colimit R Ω)
        (colimitPointPrime (R := R) (Ω := Ω)).ResidueField
        (toColimit (R := R) (Ω := Ω) X x)) = X.point x
  rw [show residuePoint (R := R) (Ω := Ω) (Field.toIsField Ω)
      (algebraMap (Colimit R Ω)
        (colimitPointPrime (R := R) (Ω := Ω)).ResidueField
        (toColimit (R := R) (Ω := Ω) X x)) =
      colimitPoint (R := R) (Ω := Ω)
        (toColimit (R := R) (Ω := Ω) X x) by
    exact Ideal.ResidueField.liftₐ_algebraMap
      (colimitPointPrime (R := R) (Ω := Ω))
      (colimitPoint (R := R) (Ω := Ω)) le_rfl
      (fun y hy ↦ colimitPoint_isUnit_of_mem_primeCompl
        (R := R) (Ω := Ω) (Field.toIsField Ω) ⟨y, hy⟩) _]
  exact DFunLike.congr_fun
    (colimitPoint_comp_toColimit (R := R) (Ω := Ω) X) x

/-- A monic polynomial with a simple residue root descends to a pointed etale stage, where the
chosen geometric point is a simple root of the descended polynomial. -/
theorem exists_stage_polynomial_with_simple_point
    (f : (LocalColimit R Ω)[X]) (hf : f.Monic)
    (a₀ : IsLocalRing.ResidueField (LocalColimit R Ω))
    (ha₀ : aeval a₀ f = 0) (hda₀ : aeval a₀ f.derivative ≠ 0) :
    ∃ (X : PointedEtaleNeighborhood R Ω) (F : X[X]),
      F.map (toLocalColimitAlgHom (R := R) (Ω := Ω) X).toRingHom = f ∧
      F.Monic ∧ F.eval₂ X.point.toRingHom
        (residueFieldAlgEquiv (R := R) (Ω := Ω) a₀) = 0 ∧
      F.derivative.eval₂ X.point.toRingHom
        (residueFieldAlgEquiv (R := R) (Ω := Ω) a₀) ≠ 0 := by
  change f.eval₂
    (algebraMap (LocalColimit R Ω)
      (IsLocalRing.ResidueField (LocalColimit R Ω))) a₀ = 0 at ha₀
  change f.derivative.eval₂
    (algebraMap (LocalColimit R Ω)
      (IsLocalRing.ResidueField (LocalColimit R Ω))) a₀ ≠ 0 at hda₀
  let e := residueFieldAlgEquiv (R := R) (Ω := Ω)
  let z : Ω := e a₀
  obtain ⟨X, hX⟩ := exists_stage_containing_finite_localColimit_set
    (R := R) (Ω := Ω) (f.coeffs : Set (LocalColimit R Ω)) (Set.toFinite _)
  let q := toLocalColimitAlgHom (R := R) (Ω := Ω) X
  have hlifts : f ∈ Polynomial.lifts q.toRingHom :=
    (Polynomial.lifts_iff_coeffs_subset_range f).mpr hX
  obtain ⟨F, hF, -, hFmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlifts hf
  let ρ : LocalColimit R Ω →+* Ω :=
    e.toRingHom.comp (IsLocalRing.residue (LocalColimit R Ω))
  have hρq : ρ.comp q.toRingHom = X.point.toRingHom := by
    apply RingHom.ext
    intro x
    exact residueFieldAlgEquiv_residue_toLocalColimitAlgHom (R := R) (Ω := Ω) X x
  have hfΩ : f.eval₂ ρ z = 0 := by
    have h := Polynomial.hom_eval₂ f
      (algebraMap (LocalColimit R Ω)
        (IsLocalRing.ResidueField (LocalColimit R Ω)))
      e.toRingHom a₀
    rw [ha₀, map_zero] at h
    simpa [ρ, z] using h.symm
  have hdfΩ : f.derivative.eval₂ ρ z ≠ 0 := by
    intro hzero
    apply hda₀
    apply e.injective
    calc
      e (f.derivative.eval₂
          (algebraMap (LocalColimit R Ω)
            (IsLocalRing.ResidueField (LocalColimit R Ω))) a₀) =
          f.derivative.eval₂ ρ z := by
        exact Polynomial.hom_eval₂ f.derivative
          (algebraMap (LocalColimit R Ω)
            (IsLocalRing.ResidueField (LocalColimit R Ω)))
          e.toRingHom a₀
      _ = 0 := hzero
      _ = e 0 := (map_zero e).symm
  refine ⟨X, F, hF, hFmonic, ?_, ?_⟩
  · rw [← hρq, ← Polynomial.eval₂_map, hF]
    exact hfΩ
  · rw [← hρq, ← Polynomial.eval₂_map, ← Polynomial.derivative_map, hF]
    exact hdfΩ

omit [IsLocalRing R] [Algebra (IsLocalRing.ResidueField R) Ω]
  [IsScalarTower R (IsLocalRing.ResidueField R) Ω]
  [IsSepClosure (IsLocalRing.ResidueField R) Ω] in
/-- A simple root at the geometric point gives a pointed etale refinement carrying an actual
root of the polynomial. -/
theorem exists_root_refinement (X : PointedEtaleNeighborhood R Ω) (F : X[X])
    (hFmonic : F.Monic) (z : Ω) (hroot : F.eval₂ X.point.toRingHom z = 0)
    (hderiv : F.derivative.eval₂ X.point.toRingHom z ≠ 0) :
    ∃ (N : PointedEtaleNeighborhood R Ω) (j : X ⟶ N) (n : N),
      N.point n = z ∧ F.eval₂ j.hom.toRingHom n = 0 := by
  let _ : Algebra X Ω := X.point.toRingHom.toAlgebra
  let _ : IsScalarTower R X Ω :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := X) (A := Ω)
      fun r ↦ (X.point.commutes r).symm
  let P : StandardEtalePair X :=
    { f := F
      monic_f := hFmonic
      g := F.derivative
      cond := ⟨1, 0, 1, by simp⟩ }
  have hz : P.HasMap z := by
    constructor
    · exact hroot
    · exact isUnit_iff_ne_zero.mpr hderiv
  let _ : Algebra R P.Ring :=
    ((algebraMap X P.Ring).comp (algebraMap R X)).toAlgebra
  let _ : IsScalarTower R X P.Ring :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := X) (A := P.Ring) rfl
  let _ : Algebra.Etale R P.Ring := Algebra.Etale.comp R X P.Ring
  let point : P.Ring →ₐ[R] Ω := (P.lift z hz).restrictScalars R
  let base : X →ₐ[R] P.Ring := IsScalarTower.toAlgHom R X P.Ring
  have hpoint : point.comp base = X.point := by
    ext x
    change P.lift z hz (algebraMap X P.Ring x) = X.point x
    exact (P.lift z hz).commutes x
  let N := ofEtaleAlgebra P.Ring point
  let j : X ⟶ N := homToOfEtaleAlgebra P.Ring point base hpoint
  let n : N := (ofEtaleAlgebraEquiv P.Ring point).symm P.X
  refine ⟨N, j, n, ?_, ?_⟩
  · change point ((ofEtaleAlgebraEquiv P.Ring point)
      ((ofEtaleAlgebraEquiv P.Ring point).symm P.X)) = z
    rw [AlgEquiv.apply_symm_apply]
    exact P.lift_X z hz
  · apply (ofEtaleAlgebraEquiv P.Ring point).injective
    let E := ofEtaleAlgebraEquiv P.Ring point
    have hcomp : E.toRingEquiv.toRingHom.comp j.hom.toRingHom = algebraMap X P.Ring := by
      apply RingHom.ext
      intro x
      change E (E.symm (base x)) = algebraMap X P.Ring x
      rw [AlgEquiv.apply_symm_apply]
      rfl
    have hn : E.toRingEquiv.toRingHom n = P.X := by
      exact AlgEquiv.apply_symm_apply E P.X
    have h := Polynomial.hom_eval₂ F j.hom.toRingHom
      E.toRingEquiv.toRingHom n
    rw [hcomp, hn,
      show F.eval₂ (algebraMap X P.Ring) P.X = 0 by
        exact P.hasMap_X.1] at h
    simpa using h

/-- The simple-root lifting clause for the local colimit.  This is clause 2 of
`HenselianLocalRing.TFAE`. -/
theorem exists_root_lifting_simple_residue_root
    (f : (LocalColimit R Ω)[X]) (hf : f.Monic)
    (a₀ : IsLocalRing.ResidueField (LocalColimit R Ω))
    (ha₀ : aeval a₀ f = 0) (hda₀ : aeval a₀ f.derivative ≠ 0) :
    ∃ a : LocalColimit R Ω,
      f.IsRoot a ∧ IsLocalRing.residue (LocalColimit R Ω) a = a₀ := by
  obtain ⟨X, F, hF, hFmonic, hroot, hderiv⟩ :=
    exists_stage_polynomial_with_simple_point (R := R) (Ω := Ω) f hf a₀ ha₀ hda₀
  let z : Ω := residueFieldAlgEquiv (R := R) (Ω := Ω) a₀
  obtain ⟨N, j, n, hnpoint, hnroot⟩ :=
    exists_root_refinement (R := R) (Ω := Ω) X F hFmonic z hroot hderiv
  let qX := toLocalColimitAlgHom (R := R) (Ω := Ω) X
  let qN := toLocalColimitAlgHom (R := R) (Ω := Ω) N
  let a : LocalColimit R Ω := qN n
  have hnat : qN.comp j.hom = qX :=
    toLocalColimitAlgHom_naturality (R := R) (Ω := Ω) j
  have hFa : F.eval₂ qX.toRingHom a = 0 := by
    have h := Polynomial.hom_eval₂ F j.hom.toRingHom qN.toRingHom n
    rw [hnroot, map_zero] at h
    have hnat' : qN.toRingHom.comp j.hom.toRingHom = qX.toRingHom :=
      congrArg AlgHom.toRingHom hnat
    rw [hnat'] at h
    exact h.symm
  refine ⟨a, ?_, ?_⟩
  · change f.eval a = 0
    rw [← hF, Polynomial.eval_map]
    exact hFa
  · let e := residueFieldAlgEquiv (R := R) (Ω := Ω)
    apply e.injective
    calc
      e (IsLocalRing.residue (LocalColimit R Ω) a) = N.point n := by
        exact residueFieldAlgEquiv_residue_toLocalColimitAlgHom
          (R := R) (Ω := Ω) N n
      _ = z := hnpoint
      _ = e a₀ := rfl

/-- The local colimit of pointed etale neighbourhoods is henselian. -/
theorem localColimit_henselianLocalRing :
    HenselianLocalRing (LocalColimit R Ω) := by
  apply ((HenselianLocalRing.TFAE (LocalColimit R Ω)).out 2 1).mp
  intro f hf a₀ ha₀ hda₀
  exact exists_root_lifting_simple_residue_root
    (R := R) (Ω := Ω) f hf a₀ ha₀ hda₀

/-- The localized filtered colimit of pointed etale neighbourhoods is strictly henselian. -/
instance localColimit_strictlyHenselianLocalRing :
    StrictlyHenselianLocalRing (LocalColimit R Ω) where
  toHenselianLocalRing := localColimit_henselianLocalRing (R := R) (Ω := Ω)
  isSepClosed_residueField := residueField_isSepClosed (R := R) (Ω := Ω)

end Pcf.Stacks.PointedEtaleNeighborhood
