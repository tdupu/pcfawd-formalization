/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Pcf.Stacks.Purity.HartogsAlgebra

/-!
# Sheaf-theoretic Hartogs recovery for a normal local domain

The fraction-intersection calculation of `HartogsAlgebra` is transferred here to sections of the
structure sheaf on the punctured spectrum.  We first express a section on a principal open as a
fraction in the function field.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.IsAffineOpen
set_option linter.style.haveILetI false

universe u

namespace Pcf.Stacks

/-- A section on a principal open is represented in the function field by a fraction whose
denominator is a power of the defining element. -/
theorem basicOpen_germ_fraction (R : CommRingCat.{u}) [IsDomain R]
    (x : R) (U : (Spec R).Opens) [Nonempty U]
    (hU : U = PrimeSpectrum.basicOpen x) (s : Γ(Spec R, U)) :
    ∃ (a : R) (n : ℕ),
      (Spec R).germToFunctionField U s * algebraMap R (Spec R).functionField (x ^ n) =
        algebraMap R (Spec R).functionField a := by
  subst U
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen x
  letI : Algebra R Γ(Spec R, U) := inferInstance
  have hgen : genericPoint (Spec R) ∈ U :=
    ((genericPoint_spec (Spec R)).mem_open_set_iff U.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U))
  have ht (r : R) :
      (Spec R).germToFunctionField U (algebraMap R Γ(Spec R, U) r) =
        algebraMap R (Spec R).functionField r := by
    exact StructureSheaf.algebraMap_germ_apply U (genericPoint (Spec R)) hgen r
  let t : Γ(Spec R, U) := s
  let d := IsLocalization.Away.sec x t
  refine ⟨d.1, d.2, ?_⟩
  have hs := IsLocalization.Away.sec_spec x t
  have hs' := congrArg (fun z : Γ(Spec R, U) => (Spec R).germToFunctionField U z) hs
  simpa only [map_mul, ht] using hs'

/-- Hartogs surjectivity for the punctured spectrum of a normal Noetherian local domain of
dimension at least two.  Every section is the restriction of an element of the base ring. -/
theorem puncturedSpectrum_algebraMap_surjective (R : CommRingCat.{u})
    [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (hdim : 2 ≤ ringKrullDim R) :
    Function.Surjective
      (algebraMap R Γ(Spec R, puncturedSpectrum R)) := by
  let X := Spec R
  let U : X.Opens := puncturedSpectrum R
  obtain ⟨x, y, hxm, hym, hx, hy, hinter⟩ :=
    exists_fraction_intersection_pair_of_isIntegrallyClosed hdim
  let Vx : X.Opens := PrimeSpectrum.basicOpen x
  let Vy : X.Opens := PrimeSpectrum.basicOpen y
  have hVx : Vx ≤ U := by
    intro p hp
    change p ≠ IsLocalRing.closedPoint R
    intro heq
    have hnot : x ∉ p.asIdeal := (PrimeSpectrum.mem_basicOpen x p).mp hp
    rw [heq] at hnot
    exact hnot hxm
  have hVy : Vy ≤ U := by
    intro p hp
    change p ≠ IsLocalRing.closedPoint R
    intro heq
    have hnot : y ∉ p.asIdeal := (PrimeSpectrum.mem_basicOpen y p).mp hp
    rw [heq] at hnot
    exact hnot hym
  have hgenx : genericPoint X ∈ Vx := by
    simp only [X, Vx, genericPoint_eq_bot_of_affine]
    exact (PrimeSpectrum.mem_basicOpen x ⊥).2 (by simpa using hx)
  have hgeny : genericPoint X ∈ Vy := by
    simp only [X, Vy, genericPoint_eq_bot_of_affine]
    exact (PrimeSpectrum.mem_basicOpen y ⊥).2 (by simpa using hy)
  letI : Nonempty Vx := ⟨⟨genericPoint X, hgenx⟩⟩
  letI : Nonempty Vy := ⟨⟨genericPoint X, hgeny⟩⟩
  letI : Nonempty U := ⟨⟨genericPoint X, hVx hgenx⟩⟩
  letI : Algebra R Γ(X, U) := inferInstance
  intro s
  let sx : Γ(X, Vx) := X.presheaf.map (homOfLE hVx).op s
  let sy : Γ(X, Vy) := X.presheaf.map (homOfLE hVy).op s
  obtain ⟨a, n, ha⟩ := basicOpen_germ_fraction (.of R) x Vx rfl sx
  obtain ⟨b, m, hb⟩ := basicOpen_germ_fraction (.of R) y Vy rfl sy
  have hgx : X.germToFunctionField Vx sx = X.germToFunctionField U s :=
    X.presheaf.germ_res_apply (homOfLE hVx) (genericPoint X) hgenx s
  have hgy : X.germToFunctionField Vy sy = X.germToFunctionField U s :=
    X.presheaf.germ_res_apply (homOfLE hVy) (genericPoint X) hgeny s
  let z : X.functionField := X.germToFunctionField U s
  have hDx : algebraMap R X.functionField (x ^ n) ≠ 0 := by
    intro h
    exact pow_ne_zero n hx (IsFractionRing.injective R X.functionField (by simpa using h))
  have hDy : algebraMap R X.functionField (y ^ m) ≠ 0 := by
    intro h
    exact pow_ne_zero m hy (IsFractionRing.injective R X.functionField (by simpa using h))
  have hfracx : algebraMap R X.functionField a /
      algebraMap R X.functionField (x ^ n) = z :=
    (div_eq_iff hDx).mpr (by change _ = X.germToFunctionField U s * _; rw [← hgx]; exact ha.symm)
  have hfracy : algebraMap R X.functionField b /
      algebraMap R X.functionField (y ^ m) = z :=
    (div_eq_iff hDy).mpr (by change _ = X.germToFunctionField U s * _; rw [← hgy]; exact hb.symm)
  obtain ⟨c, hc⟩ := hinter m n (hfracx.trans hfracy.symm)
  refine ⟨c, ?_⟩
  apply X.germToFunctionField_injective U
  have ht : X.germToFunctionField U (algebraMap R Γ(X, U) c) =
      algebraMap R X.functionField c :=
    StructureSheaf.algebraMap_germ_apply U (genericPoint X) (hVx hgenx) c
  change X.germToFunctionField U (algebraMap R Γ(X, U) c) = X.germToFunctionField U s
  rw [ht]
  exact hc.symm.trans hfracx

/-- The usual ring-level formulation of Hartogs: restriction from the entire affine scheme to
its punctured spectrum is surjective. -/
theorem puncturedSpectrum_restriction_surjective (R : Type u)
    [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (hdim : 2 ≤ ringKrullDim R) :
    Function.Surjective
      ((Spec (.of R)).presheaf.map
        (homOfLE le_top : puncturedSpectrum R ⟶ ⊤).op) := by
  intro s
  obtain ⟨c, hc⟩ :=
    puncturedSpectrum_algebraMap_surjective (.of R) hdim s
  refine ⟨(Scheme.ΓSpecIso (.of R)).inv c, ?_⟩
  exact hc

/-- The ring-level Hartogs isomorphism for a normal Noetherian local domain of dimension at
least two. -/
theorem puncturedSpectrum_restriction_bijective (R : Type u)
    [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (hdim : 2 ≤ ringKrullDim R) :
    Function.Bijective
      ((Spec (.of R)).presheaf.map
        (homOfLE le_top : puncturedSpectrum R ⟶ ⊤).op) :=
  ⟨puncturedSpectrum_restriction_injective R (le_trans (by norm_num) hdim),
    puncturedSpectrum_restriction_surjective R hdim⟩

/-- The canonical algebra map from a normal local domain to regular functions on its punctured
spectrum is an isomorphism of commutative rings. -/
theorem isIso_puncturedSpectrum_algebraMap (R : CommRingCat.{u})
    [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (hdim : 2 ≤ ringKrullDim R) :
    IsIso (CommRingCat.ofHom
      (algebraMap R Γ(Spec R, puncturedSpectrum R))) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro a b h
    apply IsFractionRing.injective R (Spec R).functionField
    have hgen : Nonempty (puncturedSpectrum R) :=
      puncturedSpectrum_nonempty_of_one_le_ringKrullDim R
        (le_trans (by norm_num) hdim)
    letI : Nonempty (puncturedSpectrum R) := hgen
    have hpoint : genericPoint (Spec R) ∈ puncturedSpectrum R :=
      ((genericPoint_spec (Spec R)).mem_open_set_iff
        (puncturedSpectrum R).isOpen).mpr (by simpa using hgen)
    have hg := congrArg (fun s : Γ(Spec R, puncturedSpectrum R) =>
      (Spec R).germToFunctionField (puncturedSpectrum R) s) h
    change (Spec R).germToFunctionField (puncturedSpectrum R)
      (algebraMap R Γ(Spec R, puncturedSpectrum R) a) =
      (Spec R).germToFunctionField (puncturedSpectrum R)
        (algebraMap R Γ(Spec R, puncturedSpectrum R) b) at hg
    have ht (r : R) :
        (Spec R).germToFunctionField (puncturedSpectrum R)
          (algebraMap R Γ(Spec R, puncturedSpectrum R) r) =
            algebraMap R (Spec R).functionField r :=
      StructureSheaf.algebraMap_germ_apply (puncturedSpectrum R)
        (genericPoint (Spec R)) hpoint r
    rw [ht a, ht b] at hg
    exact hg
  · exact puncturedSpectrum_algebraMap_surjective R hdim

end Pcf.Stacks
