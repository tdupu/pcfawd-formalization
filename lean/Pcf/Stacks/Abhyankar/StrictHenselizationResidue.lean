/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Stacks.Abhyankar.StrictHenselizationConstruction
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Etale.StandardEtale

/-!
# The residue field of the pointed-etale filtered colimit

Let `R` be local, let `k` be its residue field, and let `Ω` be a separable closure of `k`.
The point of the filtered colimit of pointed etale `R`-algebras induces an embedding of its
residue field into `Ω`.  This file proves that the embedding is surjective.

For `z : Ω`, lift the monic separable minimal polynomial of `z` from `k[X]` to `R[X]`.
Localizing its monogenic algebra away from the derivative gives a standard etale algebra with
a point sending its distinguished element to `z`.  The resulting element of the filtered
colimit provides the required residue-field preimage.
-/

open CategoryTheory Polynomial

universe u

namespace Pcf.Stacks.PointedEtaleNeighborhood

variable {R Ω : Type u} [CommRing R] [IsLocalRing R] [Field Ω]
  [Algebra R Ω] [Algebra (IsLocalRing.ResidueField R) Ω]
  [IsScalarTower R (IsLocalRing.ResidueField R) Ω]
  [IsSepClosure (IsLocalRing.ResidueField R) Ω]

/-- Every element of the chosen separable closure occurs as the value of an element in a
pointed etale neighbourhood. -/
theorem exists_pointedEtaleNeighborhood_point_eq (z : Ω) :
    ∃ (X : PointedEtaleNeighborhood R Ω) (x : X), X.point x = z := by
  let k := IsLocalRing.ResidueField R
  let p : k[X] := minpoly k z
  obtain ⟨F, hF, -, hFmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.map_surjective (IsLocalRing.residue R) IsLocalRing.residue_surjective p)
    (minpoly.monic (Algebra.IsSeparable.isSeparable k z).isIntegral)
  let P : StandardEtalePair R :=
    { f := F
      monic_f := hFmonic
      g := F.derivative
      cond := ⟨1, 0, 1, by simp⟩ }
  have htower : (algebraMap k Ω).comp (IsLocalRing.residue R) =
      (RingHom.id Ω).comp (algebraMap R Ω) := by
    rw [← IsLocalRing.ResidueField.algebraMap_eq R, RingHom.id_comp]
    exact (IsScalarTower.algebraMap_eq R k Ω).symm
  have hroot : aeval z F = 0 := by
    have hbase := Polynomial.map_aeval_eq_aeval_map
      (φ := IsLocalRing.residue R) (ψ := RingHom.id Ω) htower F z
    rw [RingHom.id_apply, RingHom.id_apply, hF] at hbase
    exact hbase.trans (minpoly.aeval k z)
  have hderiv : IsUnit (aeval z F.derivative) := by
    apply isUnit_iff_ne_zero.mpr
    have hbase := Polynomial.map_aeval_eq_aeval_map
      (φ := IsLocalRing.residue R) (ψ := RingHom.id Ω) htower F.derivative z
    rw [RingHom.id_apply, RingHom.id_apply, ← derivative_map, hF] at hbase
    rw [hbase]
    exact (Algebra.IsSeparable.isSeparable k z).aeval_derivative_ne_zero
      (minpoly.aeval k z)
  have hz : P.HasMap z := ⟨hroot, hderiv⟩
  let point : P.Ring →ₐ[R] Ω := P.lift z hz
  let N := ofEtaleAlgebra P.Ring point
  let x : N := (ofEtaleAlgebraEquiv P.Ring point).symm P.X
  refine ⟨N, x, ?_⟩
  change point ((ofEtaleAlgebraEquiv P.Ring point)
    ((ofEtaleAlgebraEquiv P.Ring point).symm P.X)) = z
  rw [AlgEquiv.apply_symm_apply]
  exact P.lift_X z hz

/-- The canonical residue-point embedding onto the chosen separable closure is surjective. -/
theorem residuePoint_surjective :
    Function.Surjective (residuePoint (R := R) (Ω := Ω) (Field.toIsField Ω)) := by
  intro z
  obtain ⟨X, x, hx⟩ := exists_pointedEtaleNeighborhood_point_eq (R := R) (Ω := Ω) z
  refine ⟨algebraMap (Colimit R Ω)
    (colimitPointPrime (R := R) (Ω := Ω)).ResidueField
    (toColimit (R := R) (Ω := Ω) X x), ?_⟩
  rw [show residuePoint (R := R) (Ω := Ω) (Field.toIsField Ω)
      (algebraMap (Colimit R Ω)
        (colimitPointPrime (R := R) (Ω := Ω)).ResidueField
        (toColimit (R := R) (Ω := Ω) X x)) =
      colimitPoint (R := R) (Ω := Ω) (toColimit (R := R) (Ω := Ω) X x) by
    exact Ideal.ResidueField.liftₐ_algebraMap
      (colimitPointPrime (R := R) (Ω := Ω))
      (colimitPoint (R := R) (Ω := Ω)) le_rfl
      (fun y hy ↦ colimitPoint_isUnit_of_mem_primeCompl
        (R := R) (Ω := Ω) (Field.toIsField Ω) ⟨y, hy⟩) _]
  exact (DFunLike.congr_fun
    (colimitPoint_comp_toColimit (R := R) (Ω := Ω) X) x).trans hx

/-- The canonical residue-point map is a bijection. -/
theorem residuePoint_bijective :
    Function.Bijective (residuePoint (R := R) (Ω := Ω) (Field.toIsField Ω)) :=
  ⟨residuePoint_injective (R := R) (Ω := Ω) (Field.toIsField Ω),
    residuePoint_surjective (R := R) (Ω := Ω)⟩

/-- The residue field of the localized filtered colimit is the chosen separable closure. -/
noncomputable def residueFieldAlgEquiv :
    (colimitPointPrime (R := R) (Ω := Ω)).ResidueField ≃ₐ[R] Ω :=
  AlgEquiv.ofBijective (residuePoint (R := R) (Ω := Ω) (Field.toIsField Ω))
    (residuePoint_bijective (R := R) (Ω := Ω))

/-- The residue field of the localized filtered colimit is separably closed. -/
theorem residueField_isSepClosed :
    IsSepClosed (colimitPointPrime (R := R) (Ω := Ω)).ResidueField := by
  let e := residueFieldAlgEquiv (R := R) (Ω := Ω)
  let _ : IsSepClosed Ω := IsSepClosure.sep_closed (IsLocalRing.ResidueField R)
  constructor
  intro p hp
  have hs : (p.map e.toRingEquiv.toRingHom).Splits :=
    IsSepClosed.splits_of_separable _ hp.map
  have hs' := hs.map e.symm.toRingEquiv.toRingHom
  have hcomp : e.symm.toRingEquiv.toRingHom.comp e.toRingEquiv.toRingHom =
      RingHom.id _ := by
    apply RingHom.ext
    intro x
    exact e.symm_apply_apply x
  rw [Polynomial.map_map, hcomp, Polynomial.map_id] at hs'
  exact hs'

end Pcf.Stacks.PointedEtaleNeighborhood
