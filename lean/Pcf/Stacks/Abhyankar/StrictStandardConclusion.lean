/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.StrictHenselizationStandardDescent
public import Pcf.Stacks.Abhyankar.StrictHenselizationDimension
public import Pcf.Stacks.Common.EtaleRegular
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# From a strict-local presentation to the Abhyankar conclusion (Stacks `0EYG`, descent)

Paragraph 2 of the proof of Stacks Tag `0EYG` (Lemma 58.31.5):

> Write `A^sh = colim A_λ` as a filtered colimit of étale `A`-algebras `A_λ`. The displayed
> isomorphism descends to an isomorphism `A_λ ⊗_A B ≅ ∏ (A_λ)_f[x]/(x^{e_i} − f)` for suitably
> large `λ`, see for example Algebra, Lemma 10.127.8. After increasing `λ` a bit more we may
> assume `e_i` is invertible in `A_λ`. Then `Spec(A_λ) → Spec(A)` is the desired étale
> neighbourhood of `x`.

This is the terminal bookkeeping of the proof: once the normalization after strict
henselization has been identified with a finite disjoint union of standard tame covers, `05N9`
descent supplies one pointed étale stage, which is packaged as the conclusion
`HasAbhyankarStandardCoverAt`.  No characteristic hypothesis is used: the exponents are units in
the strict henselization by the strict-local presentation itself, and "after increasing `λ` a bit
more" is carried out by `exists_stage_isUnit_natCast`, which descends the inverse of each `e_i` to
a stage and then the identity `e_i · e_i⁻¹ = 1` to a further stage
(`exists_refinement_eq_zero_of_toLocalColimitAlgHom_eq_zero`).  Both theorems for `0EYG` in pcf
(tame and characteristic zero) use this file through their shared proof.

## Correspondence with the Stacks proof

* `A^sh = colim A_λ`, étale `A_λ` → `PointedEtaleNeighborhood.LocalColimit R Ω`
* descent of the isomorphism (10.127.8) → `exists_stage_standardTameCover_of_limit_equiv`
* descent of the units `u_i` of the pieces → `exists_stage_units`
* "after increasing `λ` ... `e_i` invertible in `A_λ`" → `exists_stage_isUnit_natCast`
* `Spec(A_λ) → Spec(A)` is the étale neighbourhood → `hasAbhyankarStandardCoverAt_of_strict`

The only difference from Stacks is that the colimit is taken over the explicit category
`PointedEtaleNeighborhood R Ω` of pointed étale neighbourhoods.
-/

@[expose] public section

open CategoryTheory Limits
open TensorProduct

universe u

namespace Pcf.Stacks.PointedEtaleNeighborhood

open Pcf.Stacks.EtaleDescent
open Pcf.Stacks.EtaleDescent.StageAlgebra
open Pcf.Stacks.EtaleDescent.StageAlgebra.EquivalenceDescent

variable {R Ω : Type u} [CommRing R] [Field Ω] [Algebra R Ω]

set_option linter.style.haveILetI false

/-- **"After increasing `λ` a bit more we may assume `e_i` is invertible in `A_λ`"** (Stacks
`0EYG`, proof, paragraph 2).  A finite family of natural numbers that are units in the strict
local colimit is a family of units at one pointed étale stage.

The inverse of each `e_j` lives at some stage (`exists_stage_containing_finite_localColimit_set`),
and the identity `e_j · e_j⁻¹ = 1`, which holds in the colimit, holds at a further stage
(`exists_refinement_eq_zero_of_toLocalColimitAlgHom_eq_zero`); a common refinement of these
finitely many stages does the job. -/
theorem exists_stage_isUnit_natCast (i : Type) [Finite i] (e : i → ℕ)
    (h : ∀ j, IsUnit ((e j : ℕ) : LocalColimit R Ω)) :
    ∃ X : PointedEtaleNeighborhood R Ω, ∀ j, IsUnit ((e j : ℕ) : X) := by
  classical
  letI := Fintype.ofFinite i
  let v : i → LocalColimit R Ω := fun j ↦ ((h j).unit⁻¹ : (LocalColimit R Ω)ˣ)
  obtain ⟨X, hX⟩ := exists_stage_containing_finite_localColimit_set (R := R) (Ω := Ω)
    (Set.range v) (Set.finite_range v)
  choose w hw using fun j : i ↦ hX (Set.mem_range_self j)
  have hzero (j : i) :
      toLocalColimitAlgHom (R := R) (Ω := Ω) X (((e j : ℕ) : X) * w j - 1) = 0 := by
    rw [map_sub, map_mul, map_natCast, map_one, hw j]
    change ((e j : ℕ) : LocalColimit R Ω) * ((h j).unit⁻¹ : (LocalColimit R Ω)ˣ) - 1 = 0
    rw [sub_eq_zero]
    exact (h j).mul_val_inv
  choose Y f hf using fun j : i ↦
    exists_refinement_eq_zero_of_toLocalColimitAlgHom_eq_zero (R := R) (Ω := Ω) X _ (hzero j)
  obtain ⟨Z, hZ⟩ := IsFiltered.sup_objs_exists (Finset.univ.image Y)
  have hY (j : i) : Y j ∈ Finset.univ.image Y :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  let g (j : i) : Y j ⟶ Z := (hZ (hY j)).some
  refine ⟨Z, fun j ↦ ?_⟩
  have hmul : ((e j : ℕ) : Z) * (g j).hom ((f j).hom (w j)) = 1 := by
    have := congrArg (g j).hom (hf j)
    simpa only [map_sub, map_mul, map_natCast, map_one, map_zero, sub_eq_zero] using this
  exact isUnit_iff_exists_inv.mpr ⟨(g j).hom ((f j).hom (w j)), hmul⟩

/-- **The descent paragraph of Stacks `0EYG` (proof, paragraph 2), without a characteristic
hypothesis.**  A strict-local standard presentation of the normalization descends to one pointed
étale stage: the isomorphism descends by `05N9`/10.127.8
(`exists_stage_standardTameCover_of_limit_equiv`), the units of the pieces descend by
`exists_stage_units`, and the exponents become units at a stage by `exists_stage_isUnit_natCast`
("after increasing `λ` a bit more").

No characteristic hypothesis is needed: the invertibility of the exponents is read off the
strict-local presentation (where Stacks has "each `e_i` is an integer invertible in `A^sh`"). -/
theorem exists_pointedEtale_standardTameCover_of_strict
    {S : Type u} [CommRing S] [Algebra R S] [IsNoetherianRing R]
    (a : R) [Module.Finite R S]
    (hstrict : IsFiniteDisjointUnionOfStandardTameCovers
      (LocalColimit R Ω) (TensorProduct R (LocalColimit R Ω) S)
      (algebraMap R (LocalColimit R Ω) a)) :
    ∃ X : PointedEtaleNeighborhood R Ω,
      IsFiniteDisjointUnionOfStandardTameCovers X
        (X ⊗[R] S) (algebraMap R X a) := by
  classical
  let L := LocalColimit R Ω
  rcases hstrict with
    ⟨ι, hι, exponent, unit, hexponent, hexponentUnit, ⟨hstrictEquiv⟩⟩
  letI := hι
  obtain ⟨X₀, unitX₀, hunitX₀⟩ := exists_stage_units ι unit
  obtain ⟨X₁, hX₁⟩ := exists_stage_isUnit_natCast (R := R) (Ω := Ω) ι exponent hexponentUnit
  obtain ⟨X, ⟨f₀⟩, ⟨f₁⟩⟩ := exists_common_refinement (R := R) (Ω := Ω) X₀ X₁
  let unitX : ι → Xˣ := fun j ↦ Units.map f₀.hom.toMonoidHom (unitX₀ j)
  have hunitX : ∀ j, Units.map (toLocalColimitAlgHom (R := R) (Ω := Ω) X) (unitX j) = unit j := by
    intro j
    rw [← hunitX₀ j]
    apply Units.ext
    change toLocalColimitAlgHom (R := R) (Ω := Ω) X (f₀.hom (unitX₀ j : X₀)) =
      toLocalColimitAlgHom (R := R) (Ω := Ω) X₀ (unitX₀ j : X₀)
    exact DFunLike.congr_fun (toLocalColimitAlgHom_naturality (R := R) (Ω := Ω) f₀)
      (unitX₀ j : X₀)
  have hexpX : ∀ j, IsUnit ((exponent j : ℕ) : X) := fun j ↦ by
    simpa only [map_natCast] using (hX₁ j).map f₁.hom
  let F := functor (R := R) (Ω := Ω)
  let c := localCocone (R := R) (Ω := Ω)
  let G := F ⋙ Under.forget (CommRingCat.of R)
  let d := (Under.forget (CommRingCat.of R)).mapCocone c
  have hd : IsColimit d :=
    isColimitOfPreserves (Under.forget (CommRingCat.of R))
      (localCoconeIsColimit (R := R) (Ω := Ω))
  let _ : Algebra X L := (c.ι.app X).right.hom.toAlgebra
  let _ : IsScalarTower R X L :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := X) (A := L) (fun r ↦ by
      change algebraMap R L r = (c.ι.app X).right.hom (algebraMap R X r)
      exact (congr($((c.ι.app X).w).hom r)).symm)
  let A := ∀ j, AdjoinRoot
    (Pcf.LocalModel.localPoly (unitX j) (algebraMap R X a) (exponent j))
  let B := X ⊗[R] S
  letI : CommRing B := by dsimp [B]; infer_instance
  letI : Algebra X B := Algebra.TensorProduct.leftAlgebra
  letI : Algebra (G.obj X) A := by
    change Algebra X A
    infer_instance
  letI : Algebra (G.obj X) B := by
    change Algebra X B
    infer_instance
  letI : IsNoetherianRing (G.obj X) := by
    change IsNoetherianRing X
    infer_instance
  have hA : IsFiniteDisjointUnionOfStandardTameCovers X A (algebraMap R X a) :=
    ⟨ι, inferInstance, exponent, unitX, hexponent, hexpX, ⟨AlgEquiv.refl⟩⟩
  letI : Algebra.FinitePresentation R S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  letI : Algebra.FinitePresentation X B := Algebra.FinitePresentation.baseChange X
  letI : Algebra.FinitePresentation (G.obj X) B := by
    change Algebra.FinitePresentation X B
    infer_instance
  letI : Algebra L (A ⊗[X] L) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra L (B ⊗[X] L) := Algebra.TensorProduct.rightAlgebra
  have hunitXL (j : ι) : Units.map (algebraMap X L) (unitX j) = unit j := by
    exact hunitX j
  let commA : A ⊗[X] L ≃ₐ[L] L ⊗[X] A :=
    { Algebra.TensorProduct.comm X A L with
      commutes' := fun r ↦ by
        change Algebra.TensorProduct.comm X A L (1 ⊗ₜ[X] r) = r ⊗ₜ[X] 1
        rfl }
  let standardBaseChange : L ⊗[X] A ≃ₐ[L]
      ∀ j, AdjoinRoot (Pcf.LocalModel.localPoly (unit j)
        (algebraMap R L a) (exponent j)) := by
    let e₁ := standardCoversBaseChangeEquivOfUnitEq ι unitX unit hunitXL
      (algebraMap R X a) exponent
    let e₂ : (∀ j, AdjoinRoot (Pcf.LocalModel.localPoly (unit j)
        (algebraMap X L (algebraMap R X a)) (exponent j))) ≃ₐ[L]
        ∀ j, AdjoinRoot (Pcf.LocalModel.localPoly (unit j)
          (algebraMap R L a) (exponent j)) :=
      AlgEquiv.piCongrRight (fun j ↦ AdjoinRoot.algEquivOfEq L _ _ (by
        rw [IsScalarTower.algebraMap_apply R X L]))
    exact e₁.trans e₂
  let commB : B ⊗[X] L ≃ₐ[L] L ⊗[X] B :=
    { Algebra.TensorProduct.comm X B L with
      commutes' := fun r ↦ by
        change Algebra.TensorProduct.comm X B L (1 ⊗ₜ[X] r) = r ⊗ₜ[X] 1
        rfl }
  let cancelB : L ⊗[X] B ≃ₐ[L] L ⊗[R] S :=
    Algebra.TensorProduct.cancelBaseChange R X L L S
  let limitEquiv : A ⊗[X] L ≃ₐ[L] B ⊗[X] L :=
    (commA.trans standardBaseChange).trans
      ((commB.trans cancelB).trans hstrictEquiv).symm
  let limitEquiv' : LimitBaseChange G d X A ≃ₐ[LimitRing G d X]
      LimitBaseChange G d X B := by
    change A ⊗[X] L ≃ₐ[L] B ⊗[X] L
    exact limitEquiv
  obtain ⟨Y, hY⟩ := exists_stage_standardTameCover_of_limit_equiv
    (F := G) (c := d) (hc := hd)
    (i := X) (A := A) (B := B) (a := algebraMap R X a)
    hA inferInstance limitEquiv'
  rcases hY with ⟨κ, hκ, d, v, hd, hdUnit, ⟨hYEquiv⟩⟩
  let T := StageRing G X Y
  letI : Algebra X T := by
    change Algebra (G.obj X) T
    infer_instance
  letI : Algebra R T := by
    change Algebra R Y.right
    infer_instance
  letI : IsScalarTower R X T :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := X) (A := T) (fun r ↦ by
      change algebraMap R Y.right r = Y.hom.hom (algebraMap R X r)
      exact (Y.hom.hom.commutes r).symm)
  let commStage : StageBaseChange G X B Y ≃ₐ[T] T ⊗[X] B :=
    { Algebra.TensorProduct.comm X B T with
      commutes' := fun r ↦ by
        change Algebra.TensorProduct.comm X B T (1 ⊗ₜ[X] r) = r ⊗ₜ[X] 1
        rfl }
  let cancelStage : T ⊗[X] B ≃ₐ[T] T ⊗[R] S :=
    Algebra.TensorProduct.cancelBaseChange R X T T S
  let hYEquiv' : StageBaseChange G X B Y ≃ₐ[T]
      ∀ j, AdjoinRoot
        (Pcf.LocalModel.localPoly (v j) (algebraMap R T a) (d j)) :=
    hYEquiv.trans (AlgEquiv.piCongrRight (fun j ↦ AdjoinRoot.algEquivOfEq T _ _ (by
      change Pcf.LocalModel.localPoly (v j)
        (algebraMap X T (algebraMap R X a)) (d j) =
        Pcf.LocalModel.localPoly (v j) (algebraMap R T a) (d j)
      rw [IsScalarTower.algebraMap_apply R X T])))
  refine ⟨Y.right, κ, hκ, d, v, hd, hdUnit, ?_⟩
  change Nonempty (T ⊗[R] S ≃ₐ[T] ∀ j, AdjoinRoot
    (Pcf.LocalModel.localPoly (v j) (algebraMap R T a) (d j)))
  exact ⟨(commStage.trans cancelStage).symm.trans hYEquiv'⟩

/-- **"Then `Spec(A_λ) → Spec(A)` is the desired étale neighbourhood of `x`"** (Stacks `0EYG`,
proof, paragraph 2), without a characteristic hypothesis.  A strict-local standard-cover
presentation descends to the exact local standard-cover conclusion
`HasAbhyankarStandardCoverAt`: the pointed étale stage of
`exists_pointedEtale_standardTameCover_of_strict` lies over `y` (its point has kernel `y`),
is Noetherian, `a` stays a nonzerodivisor (flatness of étale maps) and `A_λ ⧸ (a)` stays regular
(`quotient_span_isRegularRing_of_etale`, Stacks `0EYH`'s Noetherian/regular clauses).  The
equality on the kernel of the chosen geometric point is the literal assertion that the pointed
étale neighbourhood lies over `y`. -/
theorem hasAbhyankarStandardCoverAt_of_strict
    {S : Type u} [CommRing S] [Algebra R S] [IsNoetherianRing R]
    (a : R) (y : PrimeSpectrum R)
    (hΩ : RingHom.ker (algebraMap R Ω) = y.asIdeal)
    (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span ({a} : Set R))]
    [Module.Finite R S]
    (hstrict : IsFiniteDisjointUnionOfStandardTameCovers
      (LocalColimit R Ω) (LocalColimit R Ω ⊗[R] S)
      (algebraMap R (LocalColimit R Ω) a)) :
    HasAbhyankarStandardCoverAt R S a y := by
  obtain ⟨X, hstandard⟩ :=
    exists_pointedEtale_standardTameCover_of_strict a hstrict
  let y' : PrimeSpectrum X :=
    ⟨RingHom.ker X.point.toRingHom, RingHom.ker_isPrime X.point.toRingHom⟩
  have hy' : y'.asIdeal.under R = y.asIdeal := by
    change (RingHom.ker X.point.toRingHom).under R = y.asIdeal
    rw [← hΩ]
    ext r
    simp only [Ideal.mem_under, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, X.point.commutes]
  let _ : IsNoetherianRing X := Algebra.FiniteType.isNoetherianRing R X
  have hmapRegular : algebraMap R X a ∈ nonZeroDivisors X := by
    letI : SMul R X := Algebra.toSMul
    letI : Module R X := Algebra.toModule
    letI : Module.Flat R X := Algebra.Smooth.flat R X
    have hsmul : IsSMulRegular X a :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors ha
    rw [mem_nonZeroDivisors_iff]
    constructor
    · intro x hx
      apply hsmul
      simpa only [Algebra.smul_def, mul_zero] using hx
    · intro x hx
      apply hsmul
      simpa only [Algebra.smul_def, mul_zero, zero_mul, mul_comm] using hx
  let _ : IsRegularRing (X ⧸ Ideal.span ({algebraMap R X a} : Set X)) :=
    quotient_span_isRegularRing_of_etale R X a
  refine ⟨X, inferInstance, inferInstance, inferInstance, ?_, inferInstance,
    hmapRegular, inferInstance, hstandard⟩
  exact ⟨y', hy'⟩

#print axioms exists_stage_isUnit_natCast
#print axioms exists_pointedEtale_standardTameCover_of_strict
#print axioms hasAbhyankarStandardCoverAt_of_strict

end Pcf.Stacks.PointedEtaleNeighborhood
