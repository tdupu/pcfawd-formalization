/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.TensorProduct.Quotient
public import Pcf.Stacks.Abhyankar.StrictHenselizationConstruction

/-!
# Base change of pointed etale neighbourhoods

This file constructs the base-change functor on the presentation-coded category of pointed
etale neighbourhoods.  It is the diagram-level input to the explicit quotient comparison in
Stacks Tag `05WS`: when the base change is `R → R ⧸ I`, its raw tensor-product object is
canonically the quotient of the original etale algebra by the extended ideal.

The comparison of the localized colimits is a further cofinality and localization argument; no
claim of the full tag is made here.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace Pcf.Stacks.PointedEtaleNeighborhood

variable {R S Ω : Type u} [CommRing R] [CommRing S] [CommRing Ω]
  [Algebra R S] [Algebra R Ω] [Algebra S Ω] [IsScalarTower R S Ω]

/-- The point on the scalar extension of a pointed etale neighbourhood. -/
noncomputable def baseChangePoint (X : PointedEtaleNeighborhood R Ω) :
    S ⊗[R] X →ₐ[S] Ω :=
  Algebra.TensorProduct.lift (Algebra.ofId S Ω) X.point (fun _ _ ↦ Commute.all _ _)

/-- The raw scalar extension of a map of pointed etale neighbourhoods. -/
noncomputable def baseChangeRawMap {X Y : PointedEtaleNeighborhood R Ω} (f : X ⟶ Y) :
    S ⊗[R] X →ₐ[S] S ⊗[R] Y :=
  Algebra.TensorProduct.map (AlgHom.id S S) f.hom

@[simp]
theorem baseChangePoint_comp_baseChangeRawMap
    {X Y : PointedEtaleNeighborhood R Ω} (f : X ⟶ Y) :
    (baseChangePoint (S := S) Y).comp (baseChangeRawMap (S := S) f) =
      baseChangePoint (S := S) X := by
  ext x
  simpa [baseChangePoint, baseChangeRawMap] using DFunLike.congr_fun f.point_comp x

noncomputable instance (X : PointedEtaleNeighborhood R Ω) :
    Algebra.Etale S (S ⊗[R] X) :=
  Algebra.Etale.baseChange R X S

/-- A scalar-extended pointed etale neighbourhood, re-encoded by a finite presentation over the
new base. -/
noncomputable abbrev baseChangeObj (X : PointedEtaleNeighborhood R Ω) :
    PointedEtaleNeighborhood S Ω :=
  ofEtaleAlgebra (S ⊗[R] X) (baseChangePoint (S := S) X)

/-- Base change of a pointed map, conjugated by the chosen finite presentation models. -/
noncomputable def baseChangeMap {X Y : PointedEtaleNeighborhood R Ω} (f : X ⟶ Y) :
    baseChangeObj (S := S) X ⟶ baseChangeObj (S := S) Y where
  hom :=
    (ofEtaleAlgebraEquiv (S ⊗[R] Y) (baseChangePoint (S := S) Y)).symm.toAlgHom.comp
      ((baseChangeRawMap (S := S) f).comp
        (ofEtaleAlgebraEquiv (S ⊗[R] X) (baseChangePoint (S := S) X)).toAlgHom)
  point_comp := by
    ext x
    change baseChangePoint (S := S) Y
      ((ofEtaleAlgebraEquiv (S ⊗[R] Y) (baseChangePoint (S := S) Y))
        ((ofEtaleAlgebraEquiv (S ⊗[R] Y) (baseChangePoint (S := S) Y)).symm
          (baseChangeRawMap (S := S) f
            ((ofEtaleAlgebraEquiv (S ⊗[R] X) (baseChangePoint (S := S) X)) x)))) =
      baseChangePoint (S := S) X
        ((ofEtaleAlgebraEquiv (S ⊗[R] X) (baseChangePoint (S := S) X)) x)
    rw [AlgEquiv.apply_symm_apply]
    exact DFunLike.congr_fun (baseChangePoint_comp_baseChangeRawMap (S := S) f) _

@[simp]
theorem ofEtaleAlgebraEquiv_baseChangeMap_apply
    {X Y : PointedEtaleNeighborhood R Ω} (f : X ⟶ Y)
    (x : baseChangeObj (S := S) X) :
    ofEtaleAlgebraEquiv (S ⊗[R] Y) (baseChangePoint (S := S) Y)
        ((baseChangeMap (S := S) f).hom x) =
      baseChangeRawMap (S := S) f
        (ofEtaleAlgebraEquiv (S ⊗[R] X) (baseChangePoint (S := S) X) x) := by
  change
    ofEtaleAlgebraEquiv (S ⊗[R] Y) (baseChangePoint (S := S) Y)
        ((ofEtaleAlgebraEquiv (S ⊗[R] Y) (baseChangePoint (S := S) Y)).symm
          (baseChangeRawMap (S := S) f
            (ofEtaleAlgebraEquiv (S ⊗[R] X) (baseChangePoint (S := S) X) x))) = _
  rw [AlgEquiv.apply_symm_apply]

/-- Base change is functorial on presentation-coded pointed etale neighbourhoods. -/
noncomputable def baseChange :
    PointedEtaleNeighborhood R Ω ⥤ PointedEtaleNeighborhood S Ω where
  obj := baseChangeObj (S := S)
  map := baseChangeMap (S := S)
  map_id X := by
    apply Hom.ext
    ext x
    apply (ofEtaleAlgebraEquiv (S ⊗[R] X) (baseChangePoint (S := S) X)).injective
    simp [baseChangeRawMap]
  map_comp f g := by
    apply Hom.ext
    ext x
    apply (ofEtaleAlgebraEquiv _ (baseChangePoint (S := S) _)).injective
    simp [baseChangeRawMap, Algebra.TensorProduct.map_id_comp]

/-- At a quotient base change, the raw scalar extension of an algebra is the quotient by the
extended ideal.  This is the stagewise algebra equivalence used in the quotient direction of
Stacks Tag `05WS`. -/
noncomputable def quotientStageEquiv (I : Ideal R) (X : PointedEtaleNeighborhood R Ω) :
    (X ⧸ I.map (algebraMap R X)) ≃ₐ[R ⧸ I] (R ⧸ I) ⊗[R] X :=
  Algebra.TensorProduct.quotIdealMapEquivQuotTensor X I

@[simp]
theorem quotientStageEquiv_mk (I : Ideal R) (X : PointedEtaleNeighborhood R Ω) (x : X) :
    quotientStageEquiv I X (Ideal.Quotient.mk _ x) = 1 ⊗ₜ[R] x :=
  rfl

/-- If the original point kills `I`, it factors through `R ⧸ I` as an `R`-algebra map. -/
noncomputable def quotientLiftPoint (I : Ideal R)
    (hI : I ≤ RingHom.ker (algebraMap R Ω)) : R ⧸ I →ₐ[R] Ω :=
  Ideal.Quotient.liftₐ I (Algebra.ofId R Ω) fun _ hx ↦
    RingHom.mem_ker.mp (hI hx)

@[simp]
theorem quotientLiftPoint_mk (I : Ideal R)
    (hI : I ≤ RingHom.ker (algebraMap R Ω)) (r : R) :
    quotientLiftPoint I hI (Ideal.Quotient.mk I r) = algebraMap R Ω r :=
  rfl

/-- Base change along `R → R ⧸ I`, with the quotient acting on `Ω` through a chosen point over
`R`.  Taking `φ = quotientLiftPoint I hI` gives the quotient functor whenever the original point
kills `I`. -/
noncomputable def quotientBaseChange (I : Ideal R) (φ : R ⧸ I →ₐ[R] Ω) :=
  let _ : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
  let _ : IsScalarTower R (R ⧸ I) Ω :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  baseChange (R := R) (S := R ⧸ I) (Ω := Ω)

/-- The point on a quotient stage transported across the stagewise quotient/base-change
equivalence. -/
noncomputable def quotientStagePoint (I : Ideal R) (φ : R ⧸ I →ₐ[R] Ω)
    (X : PointedEtaleNeighborhood R Ω) :=
  letI : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
  letI : IsScalarTower R (R ⧸ I) Ω :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  (baseChangePoint (S := R ⧸ I) X).comp (quotientStageEquiv I X).toAlgHom

@[simp]
theorem quotientStagePoint_mk (I : Ideal R) (φ : R ⧸ I →ₐ[R] Ω)
    (X : PointedEtaleNeighborhood R Ω) (x : X) :
    quotientStagePoint I φ X (Ideal.Quotient.mk _ x) = X.point x := by
  let _ : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
  let _ : IsScalarTower R (R ⧸ I) Ω :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  dsimp only [quotientStagePoint]
  change baseChangePoint (S := R ⧸ I) X
    (quotientStageEquiv I X (Ideal.Quotient.mk _ x)) = X.point x
  rw [quotientStageEquiv_mk]
  simp [baseChangePoint]

end Pcf.Stacks.PointedEtaleNeighborhood
