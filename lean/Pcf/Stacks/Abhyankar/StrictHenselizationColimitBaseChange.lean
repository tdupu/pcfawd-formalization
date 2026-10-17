/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.StrictHenselizationBaseChange

/-!
# The canonical map to a base-changed pointed-etale colimit

Base changing every pointed etale neighbourhood from `R` to `S` gives a compatible cocone over
the original diagram with vertex the pointed-etale colimit over `S`.  This file constructs the
resulting canonical ring map on colimits.  For a quotient base change `S = R ⧸ I`, the map
factors through the quotient by the extended ideal.

Proving that this factor map is an equivalence requires cofinality of quotient base change on
pointed etale neighbourhoods (equivalently, effective lifting of pointed etale neighbourhoods
across the quotient).  That separate step is not asserted here.
-/

@[expose] public section

open CategoryTheory Limits
open scoped TensorProduct

universe u

namespace Pcf.Stacks.PointedEtaleNeighborhood

variable {R S Ω : Type u} [CommRing R] [CommRing S] [CommRing Ω]
  [Algebra R S] [Algebra R Ω] [Algebra S Ω] [IsScalarTower R S Ω]

/-- The ring map from an original pointed stage to the colimit of the base-changed diagram. -/
noncomputable def stageToBaseChangeColimit (X : PointedEtaleNeighborhood R Ω) :
    X →+* Colimit S Ω :=
  (toColimit (R := S) (Ω := Ω) (baseChangeObj (S := S) X)).toRingHom.comp
    ((ofEtaleAlgebraEquiv (S ⊗[R] X) (baseChangePoint (S := S) X)).symm.toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom)

/-- The presentation-model map for base change sends the canonical tensor of an element to the
canonical tensor of its image. -/
theorem baseChangeMap_symm_tmul
    {X Y : PointedEtaleNeighborhood R Ω} (f : X ⟶ Y) (x : X) :
    (baseChangeMap (S := S) f).hom
        ((ofEtaleAlgebraEquiv (S ⊗[R] X) (baseChangePoint (S := S) X)).symm
          (1 ⊗ₜ[R] x)) =
      (ofEtaleAlgebraEquiv (S ⊗[R] Y) (baseChangePoint (S := S) Y)).symm
        (1 ⊗ₜ[R] f.hom x) := by
  apply (ofEtaleAlgebraEquiv (S ⊗[R] Y) (baseChangePoint (S := S) Y)).injective
  rw [ofEtaleAlgebraEquiv_baseChangeMap_apply, AlgEquiv.apply_symm_apply]
  simp [baseChangeRawMap]

/-- The stage maps into the base-changed colimit are natural in the original pointed-etale
diagram. -/
theorem stageToBaseChangeColimit_naturality
    {X Y : PointedEtaleNeighborhood R Ω} (f : X ⟶ Y) :
    (stageToBaseChangeColimit (S := S) Y).comp f.hom.toRingHom =
      stageToBaseChangeColimit (S := S) X := by
  apply DFunLike.ext
  intro x
  change toColimit (R := S) (Ω := Ω) (baseChangeObj (S := S) Y)
      ((ofEtaleAlgebraEquiv (S ⊗[R] Y) (baseChangePoint (S := S) Y)).symm
        (1 ⊗ₜ[R] f.hom x)) =
    toColimit (R := S) (Ω := Ω) (baseChangeObj (S := S) X)
      ((ofEtaleAlgebraEquiv (S ⊗[R] X) (baseChangePoint (S := S) X)).symm
        (1 ⊗ₜ[R] x))
  rw [← baseChangeMap_symm_tmul (S := S) f x]
  exact congr($(colimit.w (functor (R := S) (Ω := Ω))
    (baseChangeMap (S := S) f)).right.hom _)

/-- The original pointed-etale diagram, viewed as a diagram of rings under `R`, has a cocone in
the colimit over `S` obtained by base changing each stage. -/
noncomputable def baseChangeColimitCocone :
    Cocone (functor (R := R) (Ω := Ω)) := by
  refine
    { pt := Under.mk (CommRingCat.ofHom
        ((algebraMap S (Colimit S Ω)).comp (algebraMap R S)))
      ι :=
        { app := fun X ↦ ?_
          naturality := fun X Y f ↦ ?_ } }
  · refine Under.homMk (CommRingCat.ofHom (stageToBaseChangeColimit (S := S) X)) ?_
    ext r
    change toColimit (R := S) (Ω := Ω) (baseChangeObj (S := S) X)
      ((ofEtaleAlgebraEquiv (S ⊗[R] X) (baseChangePoint (S := S) X)).symm
        (1 ⊗ₜ[R] algebraMap R X r)) =
      algebraMap S (Colimit S Ω) (algebraMap R S r)
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    change toColimit (R := S) (Ω := Ω) (baseChangeObj (S := S) X)
      ((ofEtaleAlgebraEquiv (S ⊗[R] X) (baseChangePoint (S := S) X)).symm
        (algebraMap S (S ⊗[R] X) (algebraMap R S r))) =
      algebraMap S (Colimit S Ω) (algebraMap R S r)
    rw [(ofEtaleAlgebraEquiv (S ⊗[R] X)
      (baseChangePoint (S := S) X)).symm.commutes]
    exact (toColimit (R := S) (Ω := Ω) (baseChangeObj (S := S) X)).commutes _
  · ext x
    exact DFunLike.congr_fun (stageToBaseChangeColimit_naturality (S := S) f) x

/-- The canonical ring map from the original pointed-etale colimit to the colimit after base
change. -/
noncomputable def colimitBaseChangeRingHom : Colimit R Ω →+* Colimit S Ω :=
  (colimit.desc (functor (R := R) (Ω := Ω))
    (baseChangeColimitCocone (R := R) (S := S) (Ω := Ω))).right.hom

@[simp]
theorem colimitBaseChangeRingHom_toColimit
    (X : PointedEtaleNeighborhood R Ω) (x : X) :
    colimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω)
        (toColimit (R := R) (Ω := Ω) X x) =
      stageToBaseChangeColimit (S := S) X x := by
  change (colimit.desc (functor (R := R) (Ω := Ω))
      (baseChangeColimitCocone (R := R) (S := S) (Ω := Ω))).right.hom
      ((colimit.ι (functor (R := R) (Ω := Ω)) X).right.hom x) =
    stageToBaseChangeColimit (S := S) X x
  exact congr($(colimit.ι_desc
    (baseChangeColimitCocone (R := R) (S := S) (Ω := Ω)) X).right.hom x)

/-- On the base ring, the colimit base-change map is the composite through `S`. -/
theorem colimitBaseChangeRingHom_algebraMap (r : R) :
    colimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω)
        (algebraMap R (Colimit R Ω) r) =
      algebraMap S (Colimit S Ω) (algebraMap R S r) := by
  exact congr($((colimit.desc (functor (R := R) (Ω := Ω))
    (baseChangeColimitCocone (R := R) (S := S) (Ω := Ω))).w).hom r)

/-- The canonical colimit map for quotient base change, using an `R`-point of `R ⧸ I` to give
`Ω` its quotient-algebra structure. -/
noncomputable def quotientColimitBaseChangeRingHom (I : Ideal R)
    (φ : R ⧸ I →ₐ[R] Ω) :=
  letI : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
  letI : IsScalarTower R (R ⧸ I) Ω :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  colimitBaseChangeRingHom (R := R) (S := R ⧸ I) (Ω := Ω)

@[simp]
theorem quotientColimitBaseChangeRingHom_algebraMap (I : Ideal R)
    (φ : R ⧸ I →ₐ[R] Ω) (r : R) :
    let _ : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
    quotientColimitBaseChangeRingHom I φ (algebraMap R (Colimit R Ω) r) =
      algebraMap (R ⧸ I) (Colimit (R ⧸ I) Ω) (Ideal.Quotient.mk I r) := by
  dsimp only
  let _ : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
  let _ : IsScalarTower R (R ⧸ I) Ω :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  exact colimitBaseChangeRingHom_algebraMap
    (R := R) (S := R ⧸ I) (Ω := Ω) r

/-- The ideal extended from `I` is killed by the canonical quotient-base-change map on
pointed-etale colimits. -/
theorem map_le_ker_quotientColimitBaseChangeRingHom (I : Ideal R)
    (φ : R ⧸ I →ₐ[R] Ω) :
    I.map (algebraMap R (Colimit R Ω)) ≤
      RingHom.ker (quotientColimitBaseChangeRingHom I φ) := by
  let _ : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
  let _ : IsScalarTower R (R ⧸ I) Ω :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  rw [Ideal.mem_comap, RingHom.mem_ker,
    quotientColimitBaseChangeRingHom_algebraMap]
  calc
    algebraMap (R ⧸ I) (Colimit (R ⧸ I) Ω) (Ideal.Quotient.mk I r) =
        algebraMap (R ⧸ I) (Colimit (R ⧸ I) Ω) 0 :=
      congrArg _ (Ideal.Quotient.eq_zero_iff_mem.mpr hr)
    _ = 0 := map_zero _

/-- The canonical quotient-base-change map factors through the quotient of the original colimit
by the extended ideal. -/
noncomputable def colimitQuotientBaseChangeRingHom (I : Ideal R)
    (φ : R ⧸ I →ₐ[R] Ω) :=
  letI : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
  Ideal.Quotient.lift _ (quotientColimitBaseChangeRingHom I φ)
    (fun _ hx ↦ RingHom.mem_ker.mp
      (map_le_ker_quotientColimitBaseChangeRingHom I φ hx))

@[simp]
theorem colimitQuotientBaseChangeRingHom_mk (I : Ideal R)
    (φ : R ⧸ I →ₐ[R] Ω) (x : Colimit R Ω) :
    colimitQuotientBaseChangeRingHom I φ (Ideal.Quotient.mk _ x) =
      quotientColimitBaseChangeRingHom I φ x :=
  rfl

/-- The factor map is an algebra map over the quotient base. -/
noncomputable def colimitQuotientBaseChangeAlgHom (I : Ideal R)
    (φ : R ⧸ I →ₐ[R] Ω) :=
  letI : Algebra (R ⧸ I) Ω := φ.toRingHom.toAlgebra
  letI : IsScalarTower R (R ⧸ I) Ω :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  show (Colimit R Ω ⧸ I.map (algebraMap R (Colimit R Ω))) →ₐ[R ⧸ I]
    Colimit (R ⧸ I) Ω from
  { __ := colimitQuotientBaseChangeRingHom I φ
    commutes' := by
      intro q
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
      change quotientColimitBaseChangeRingHom I φ
          (algebraMap R (Colimit R Ω) r) =
        algebraMap (R ⧸ I) (Colimit (R ⧸ I) Ω) (Ideal.Quotient.mk I r)
      exact quotientColimitBaseChangeRingHom_algebraMap I φ r }

@[simp]
theorem colimitQuotientBaseChangeAlgHom_mk (I : Ideal R)
    (φ : R ⧸ I →ₐ[R] Ω) (x : Colimit R Ω) :
    colimitQuotientBaseChangeAlgHom I φ (Ideal.Quotient.mk _ x) =
      quotientColimitBaseChangeRingHom I φ x :=
  rfl

end Pcf.Stacks.PointedEtaleNeighborhood
