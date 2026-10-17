/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.StrictHenselizationColimitBaseChange
public import Pcf.Stacks.Abhyankar.StrictHenselizationStages

/-!
# Base change on the localized pointed-etale colimit

The canonical map on pointed-etale colimits respects the geometric points.  It therefore sends
the complement of the point prime to the complement of the point prime and extends uniquely to
the localized colimits.  For quotient base change, the resulting local map factors through the
quotient by the extended ideal.

This constructs the canonical comparison map required by Stacks Tag `05WS`.  Its bijectivity is
the remaining cofinality/effective-lifting step and is not asserted here.
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Pcf.Stacks.PointedEtaleNeighborhood

variable {R S Ω : Type u} [CommRing R] [CommRing S] [Field Ω]
  [Algebra R S] [Algebra R Ω] [Algebra S Ω] [IsScalarTower R S Ω]

/-- The stage map into the base-changed colimit is compatible with the geometric point. -/
theorem colimitPoint_stageToBaseChangeColimit
    (X : PointedEtaleNeighborhood R Ω) (x : X) :
    colimitPoint (R := S) (Ω := Ω) (stageToBaseChangeColimit (S := S) X x) =
      X.point x := by
  let z := (ofEtaleAlgebraEquiv (S ⊗[R] X) (baseChangePoint (S := S) X)).symm
    (1 ⊗ₜ[R] x)
  calc
    colimitPoint (R := S) (Ω := Ω)
        (toColimit (R := S) (Ω := Ω) (baseChangeObj (S := S) X) z) =
        (baseChangeObj (S := S) X).point z := by
      exact DFunLike.congr_fun
        (colimitPoint_comp_toColimit (R := S) (Ω := Ω)
          (baseChangeObj (S := S) X)) z
    _ = X.point x := by
      change baseChangePoint (S := S) X
        ((ofEtaleAlgebraEquiv (S ⊗[R] X) (baseChangePoint (S := S) X))
          ((ofEtaleAlgebraEquiv (S ⊗[R] X) (baseChangePoint (S := S) X)).symm
            (1 ⊗ₜ[R] x))) = X.point x
      rw [AlgEquiv.apply_symm_apply]
      simp [baseChangePoint]

/-- The canonical colimit base-change map commutes with the geometric points. -/
theorem colimitPoint_comp_colimitBaseChangeRingHom :
    (colimitPoint (R := S) (Ω := Ω)).toRingHom.comp
        (colimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω)) =
      (colimitPoint (R := R) (Ω := Ω)).toRingHom := by
  apply DFunLike.ext
  intro c
  obtain ⟨X, x, rfl⟩ := exists_stage_of_colimit_element (R := R) (Ω := Ω) c
  change colimitPoint (R := S) (Ω := Ω)
      (colimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω)
        (toColimit (R := R) (Ω := Ω) X x)) =
    colimitPoint (R := R) (Ω := Ω) (toColimit (R := R) (Ω := Ω) X x)
  rw [colimitBaseChangeRingHom_toColimit,
    colimitPoint_stageToBaseChangeColimit]
  exact (DFunLike.congr_fun
    (colimitPoint_comp_toColimit (R := R) (Ω := Ω) X) x).symm

/-- The colimit base-change map sends the complement of the original point prime into the
complement of the base-changed point prime. -/
theorem colimitBaseChangeRingHom_mem_primeCompl
    (x : (colimitPointPrime (R := R) (Ω := Ω)).primeCompl) :
    colimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω) x ∈
      (colimitPointPrime (R := S) (Ω := Ω)).primeCompl := by
  apply Ideal.mem_primeCompl_iff.mpr
  intro hx
  apply (Ideal.mem_primeCompl_iff.mp x.property)
  change colimitPoint (R := R) (Ω := Ω) x = 0
  have hpoint := DFunLike.congr_fun
    (colimitPoint_comp_colimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω))
      (x : Colimit R Ω)
  have hpoint' : colimitPoint (R := S) (Ω := Ω)
      (colimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω) x) =
      colimitPoint (R := R) (Ω := Ω) x := by
    exact hpoint
  calc
    colimitPoint (R := R) (Ω := Ω) x =
        colimitPoint (R := S) (Ω := Ω)
          (colimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω) x) := hpoint'.symm
    _ = 0 := RingHom.mem_ker.mp hx

/-- The canonical map on colimits extends to the localizations at their geometric point
primes. -/
noncomputable def localColimitBaseChangeRingHom :
    LocalColimit R Ω →+* LocalColimit S Ω :=
  IsLocalization.lift
    (M := (colimitPointPrime (R := R) (Ω := Ω)).primeCompl)
    (S := LocalColimit R Ω)
    (g := (algebraMap (Colimit S Ω) (LocalColimit S Ω)).comp
      (colimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω)))
    (fun x ↦ IsLocalization.map_units (LocalColimit S Ω)
      ⟨colimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω) x,
        colimitBaseChangeRingHom_mem_primeCompl (R := R) (S := S) (Ω := Ω) x⟩)

@[simp]
theorem localColimitBaseChangeRingHom_toLocalColimit (c : Colimit R Ω) :
    localColimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω)
        (algebraMap (Colimit R Ω) (LocalColimit R Ω) c) =
      algebraMap (Colimit S Ω) (LocalColimit S Ω)
        (colimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω) c) :=
  IsLocalization.lift_eq
    (S := LocalColimit R Ω) (P := LocalColimit S Ω)
    (g := (algebraMap (Colimit S Ω) (LocalColimit S Ω)).comp
      (colimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω))) _ c

/-- The localized base-change map for a quotient base, with the quotient action on `Ω` supplied
by a chosen `R`-point. -/
noncomputable def quotientLocalColimitBaseChangeRingHom (I : Ideal R)
    (φ : R ⧸ I →ₐ[R] Ω) :=
  letI : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
  letI : IsScalarTower R (R ⧸ I) Ω :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  localColimitBaseChangeRingHom (R := R) (S := R ⧸ I) (Ω := Ω)

@[simp]
theorem quotientLocalColimitBaseChangeRingHom_algebraMap (I : Ideal R)
    (φ : R ⧸ I →ₐ[R] Ω) (r : R) :
    let _ : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
    quotientLocalColimitBaseChangeRingHom I φ
        (algebraMap R (LocalColimit R Ω) r) =
      algebraMap (R ⧸ I) (LocalColimit (R ⧸ I) Ω) (Ideal.Quotient.mk I r) := by
  dsimp only
  let _ : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
  let _ : IsScalarTower R (R ⧸ I) Ω :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  rw [IsScalarTower.algebraMap_apply R (Colimit R Ω) (LocalColimit R Ω),
    IsScalarTower.algebraMap_apply (R ⧸ I) (Colimit (R ⧸ I) Ω)
      (LocalColimit (R ⧸ I) Ω)]
  change localColimitBaseChangeRingHom (R := R) (S := R ⧸ I) (Ω := Ω)
      (algebraMap (Colimit R Ω) (LocalColimit R Ω)
        (algebraMap R (Colimit R Ω) r)) =
    algebraMap (Colimit (R ⧸ I) Ω) (LocalColimit (R ⧸ I) Ω)
      (algebraMap (R ⧸ I) (Colimit (R ⧸ I) Ω) (Ideal.Quotient.mk I r))
  rw [localColimitBaseChangeRingHom_toLocalColimit,
    colimitBaseChangeRingHom_algebraMap]
  rfl

/-- The localized quotient-base-change map kills the ideal extended from the original base. -/
theorem map_le_ker_quotientLocalColimitBaseChangeRingHom (I : Ideal R)
    (φ : R ⧸ I →ₐ[R] Ω) :
    I.map (algebraMap R (LocalColimit R Ω)) ≤
      RingHom.ker (quotientLocalColimitBaseChangeRingHom I φ) := by
  let _ : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
  let _ : IsScalarTower R (R ⧸ I) Ω :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  rw [Ideal.mem_comap, RingHom.mem_ker,
    quotientLocalColimitBaseChangeRingHom_algebraMap]
  calc
    algebraMap (R ⧸ I) (LocalColimit (R ⧸ I) Ω) (Ideal.Quotient.mk I r) =
        algebraMap (R ⧸ I) (LocalColimit (R ⧸ I) Ω) 0 :=
      congrArg _ (Ideal.Quotient.eq_zero_iff_mem.mpr hr)
    _ = 0 := map_zero _

/-- The canonical localized comparison map factors through the quotient by the ideal extended
from `R`. -/
noncomputable def localQuotientBaseChangeRingHom (I : Ideal R)
    (φ : R ⧸ I →ₐ[R] Ω) :=
  letI : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
  Ideal.Quotient.lift _ (quotientLocalColimitBaseChangeRingHom I φ)
    (fun _ hx ↦ RingHom.mem_ker.mp
      (map_le_ker_quotientLocalColimitBaseChangeRingHom I φ hx))

@[simp]
theorem localQuotientBaseChangeRingHom_mk (I : Ideal R)
    (φ : R ⧸ I →ₐ[R] Ω) (x : LocalColimit R Ω) :
    localQuotientBaseChangeRingHom I φ (Ideal.Quotient.mk _ x) =
      quotientLocalColimitBaseChangeRingHom I φ x :=
  rfl

/-- The localized quotient comparison is an algebra map over `R ⧸ I`.  Establishing that this
map is an equivalence is precisely the remaining comparison step in Tag `05WS`. -/
noncomputable def localQuotientBaseChangeAlgHom (I : Ideal R)
    (φ : R ⧸ I →ₐ[R] Ω) :=
  letI : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
  letI : IsScalarTower R (R ⧸ I) Ω :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  show (LocalColimit R Ω ⧸ I.map (algebraMap R (LocalColimit R Ω))) →ₐ[R ⧸ I]
    LocalColimit (R ⧸ I) Ω from
  { __ := localQuotientBaseChangeRingHom I φ
    commutes' := by
      intro q
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
      change quotientLocalColimitBaseChangeRingHom I φ
          (algebraMap R (LocalColimit R Ω) r) =
        algebraMap (R ⧸ I) (LocalColimit (R ⧸ I) Ω) (Ideal.Quotient.mk I r)
      exact quotientLocalColimitBaseChangeRingHom_algebraMap I φ r }

@[simp]
theorem localQuotientBaseChangeAlgHom_mk (I : Ideal R)
    (φ : R ⧸ I →ₐ[R] Ω) (x : LocalColimit R Ω) :
    localQuotientBaseChangeAlgHom I φ (Ideal.Quotient.mk _ x) =
      quotientLocalColimitBaseChangeRingHom I φ x :=
  rfl

end Pcf.Stacks.PointedEtaleNeighborhood
