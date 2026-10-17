/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.OrzechProperty
public import Mathlib.RingTheory.LocalRing.Module
public import Pcf.Stacks.Abhyankar.Scheme.Defs
public import Pcf.Stacks.Purity.LocalEtaleSectionLifting

/-!
# Finite étale covers are étale locally split (affine form of Stacks Tag `04HN`)

Stacks, Étale Morphisms, Lemma 41.18.3 (Tag `04HN`): for a finite étale `f : X → S` and `s ∈ S`
there is an étale neighbourhood `(U, u) → (S, s)` with `X_U = ∐_j V_j` and each `V_j → U` an
isomorphism.  This file proves the affine form `hasSplitCoverAt_of_finite_etale`: for `B` finite
étale over a Noetherian ring `R` and `y ∈ Spec R` there is a pointed étale `R → A` over `y` with
`A ⊗_R B ≅ A^n`.  It is used in the case `x ∉ D` of Stacks Tag `0EYG` (the proof of `0EYG`
cites `04HN` there, with `e = 1`, `f = 1` in Example `0EYF`).

## Proof route and correspondence with Stacks

The Stacks proof of `04HN` applies Lemma 41.17.3 (an unramified morphism is, étale locally on the
base, a disjoint union of closed immersions onto opens) and shrinks `U` to the intersection of the
images.  We do not follow that route; instead (as in pcf's proof of Tag `0EYG`):

| step | Lean |
| --- | --- |
| split over a strictly henselian local ring (closed fibre split, residue points lift by `09XI`, \
  Nakayama and Orzech for bijectivity) | `isFiniteSplit_of_strictlyHenselianLocalRing` |
| `LocalColimit R Ω` at `y` is strictly henselian (via `R_y`, Tag `04GW`) | \
  `localColimit_strictlyHenselianLocalRing_of_prime` |
| descend the splitting to a pointed étale stage (Tag `05N9`) | `hasSplitCoverAt_of_finite_etale` |
-/

@[expose] public section

universe u

open TensorProduct CategoryTheory Limits IsLocalRing

namespace Pcf.Stacks.SchemeLevel

set_option linter.style.haveILetI false

section StrictSplitting

variable (L T : Type u) [CommRing L] [CommRing T] [Algebra L T]

/-- **A finite étale algebra over a strictly henselian local ring is split.**

Route (not the Stacks proof of `04HN`, which goes through Étale Morphisms, Lemma 41.17.3):
the closed fibre
`κ ⊗_L T` is `κ^n` since `κ` is separably closed; the `n` residue points `T → κ` lift to
`L`-algebra maps `T → L` (henselian section lifting, Tag `09XI` local case,
`exists_algHom_lift_of_etale_of_isLocalRing`); the product map `T → L^n` is surjective by
Nakayama, and injective because `T` is free of rank `n` and a surjective endomorphism of a finite
module is injective (Orzech property). -/
theorem isFiniteSplit_of_strictlyHenselianLocalRing [StrictlyHenselianLocalRing L]
    [Module.Finite L T] [Algebra.Etale L T] : Algebra.IsFiniteSplit L T := by
  classical
  let κ := ResidueField L
  obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun κ (κ ⊗[L] T)
  -- the residue points
  let σ : Fin n → (T →ₐ[L] L ⧸ maximalIdeal L) := fun i ↦
    ((((Pi.evalAlgHom κ (fun _ : Fin n ↦ κ) i).comp e.toAlgHom).restrictScalars L).comp
      (Algebra.TensorProduct.includeRight (R := L) (A := κ) (B := T)))
  have hσ : ∀ i t, σ i t = e (1 ⊗ₜ t) i := fun i t ↦ rfl
  choose τ hτ using fun i ↦
    exists_algHom_lift_of_etale_of_isLocalRing (S := T) (maximalIdeal L) (σ i)
  have hτσ : ∀ i t, residue L (τ i t) = e (1 ⊗ₜ t) i := fun i t ↦ by
    rw [← hσ]
    exact congrArg (fun φ : T →ₐ[L] L ⧸ maximalIdeal L ↦ φ t) (hτ i)
  let τ' : T →ₐ[L] (Fin n → L) := AlgHom.pi τ
  -- surjectivity by Nakayama
  have hsurj : Function.Surjective τ' := by
    change Function.Surjective τ'.toLinearMap
    rw [← LinearMap.range_eq_top (f := τ'.toLinearMap)]
    rw [← IsLocalRing.map_mkQ_eq_top]
    rw [eq_top_iff]
    rintro x -
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ x
    obtain ⟨z, hz⟩ := e.surjective (fun i ↦ residue L (m i))
    obtain ⟨t, rfl⟩ := TensorProduct.mk_surjective L T κ Ideal.Quotient.mk_surjective z
    refine ⟨τ' t, ⟨t, rfl⟩, ?_⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    have hmem : ∀ i, (τ' t - m) i ∈ maximalIdeal L := by
      intro i
      rw [← residue_eq_zero_iff, Pi.sub_apply, map_sub]
      change residue L (τ i t) - residue L (m i) = 0
      rw [hτσ, sub_eq_zero]
      exact congrFun hz i
    have hdecomp : τ' t - m = ∑ i, (τ' t - m) i • Pi.single i (1 : L) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hdecomp]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hmem i) Submodule.mem_top
  -- injectivity by rank
  have hfree : Module.Free L T := Module.free_of_flat_of_isLocalRing
  have hrank : Module.finrank L T = Module.finrank L (Fin n → L) := by
    have hbc := Module.finrank_baseChange (R := κ) (S := L) (M' := T)
    rw [Module.finrank_fin_fun, ← hbc, e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
  let φ : T ≃ₗ[L] (Fin n → L) := LinearEquiv.ofFinrankEq T (Fin n → L) hrank
  let g : (Fin n → L) →ₗ[L] (Fin n → L) := τ'.toLinearMap ∘ₗ φ.symm.toLinearMap
  have hg : Function.Surjective g := hsurj.comp φ.symm.surjective
  have hginj : Function.Injective g := OrzechProperty.injective_of_surjective_endomorphism g hg
  have hinj : Function.Injective τ' := by
    intro s t hst
    apply φ.injective
    apply hginj
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      AlgHom.toLinearMap_apply, hst]
  exact ⟨n, ⟨AlgEquiv.ofBijective τ' ⟨hinj, hsurj⟩⟩⟩

end StrictSplitting

section Transport

/-- Strict henselianity is invariant under ring isomorphism. -/
theorem strictlyHenselianLocalRing_of_ringEquiv {L L' : Type u} [CommRing L] [CommRing L']
    [StrictlyHenselianLocalRing L'] (φ : L' ≃+* L) : StrictlyHenselianLocalRing L := by
  haveI : HenselianLocalRing L := henselianLocalRing_of_ringEquiv φ
  exact
    { isSepClosed_residueField :=
        isSepClosed_of_ringEquiv (IsLocalRing.ResidueField.mapEquiv φ) }

open PointedEtaleNeighborhood in
/-- The strict henselization `LocalColimit R Ω` at a prime `p` (`Ω = κ(p)ˢᵉᵖ`) is strictly
henselian: it is identified with the strict henselization of the local ring `R_p`
(`localColimitAtPrimeRingEquiv`, Stacks Tag `04GW`), which is strictly henselian. -/
theorem localColimit_strictlyHenselianLocalRing_of_prime {R : Type u} [CommRing R]
    (p : Ideal R) [p.IsPrime] :
    letI := geometricPointAtAlgebra p
    StrictlyHenselianLocalRing (LocalColimit R (geometricPointAt p)) := by
  let Rp := Localization.AtPrime p
  let Ω := geometricPointAt p
  letI : Algebra R Ω := geometricPointAtAlgebra p
  have hΩ : RingHom.ker (algebraMap R Ω) = p := ker_geometricPointAtAlgebra p
  letI : Algebra Rp Ω := atPrimeAlgebra p hΩ
  haveI : IsScalarTower R Rp Ω := atPrimeAlgebra_isScalarTower p hΩ
  haveI : IsScalarTower Rp (ResidueField Rp) Ω := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    apply IsLocalization.ringHom_ext p.primeCompl
    rw [← IsScalarTower.algebraMap_eq, RingHom.comp_assoc,
      IsLocalRing.ResidueField.algebraMap_eq]
    rfl
  exact strictlyHenselianLocalRing_of_ringEquiv (localColimitAtPrimeRingEquiv p hΩ).symm

end Transport

open PointedEtaleNeighborhood EtaleDescent EtaleDescent.StageAlgebra
  EtaleDescent.StageAlgebra.EquivalenceDescent in
/-- **Affine form of Stacks Tag `04HN`.**  A finite étale algebra `B` over a Noetherian ring `R`
is split by a pointed étale neighbourhood of any prime `y`: there is an étale `R → A` with a
prime over `y`, `A` Noetherian, and `A ⊗_R B ≅ A^n`.

Proof route (differs from Stacks, see the module docstring): split over the strict
henselization `LocalColimit R Ω` at `y` (`isFiniteSplit_of_strictlyHenselianLocalRing`), then
descend the isomorphism to a pointed étale stage (Tag `05N9`, `exists_descendedAlgEquiv`).
The stage lies over `y` because its geometric point has kernel over `y`. -/
theorem hasSplitCoverAt_of_finite_etale {R : Type u} [CommRing R] [IsNoetherianRing R]
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B] [Algebra.Etale R B]
    (y : PrimeSpectrum R) : HasSplitCoverAt B y := by
  classical
  let Ω := geometricPointAt y.asIdeal
  letI : Algebra R Ω := geometricPointAtAlgebra y.asIdeal
  have hΩ : RingHom.ker (algebraMap R Ω) = y.asIdeal := ker_geometricPointAtAlgebra y.asIdeal
  let L := LocalColimit R Ω
  haveI : StrictlyHenselianLocalRing L := localColimit_strictlyHenselianLocalRing_of_prime _
  -- the splitting over the strict henselization
  haveI : Algebra.IsFiniteSplit L (L ⊗[R] B) :=
    isFiniteSplit_of_strictlyHenselianLocalRing L (L ⊗[R] B)
  obtain ⟨n, ⟨hstrictEquiv⟩⟩ :=
    Algebra.IsFiniteSplit.nonempty_algEquiv_fun L (L ⊗[R] B)
  -- descent
  let X : PointedEtaleNeighborhood R Ω := ofEtaleAlgebra R (Algebra.ofId R Ω)
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
  let A := Fin n → X
  let B' := X ⊗[R] B
  letI : Algebra (G.obj X) A := by
    change Algebra X A
    infer_instance
  letI : Algebra (G.obj X) B' := by
    change Algebra X B'
    infer_instance
  letI : Algebra.FinitePresentation R B := Algebra.FinitePresentation.of_finiteType.mp
    inferInstance
  have hA : Algebra.FinitePresentation (G.obj X) A := by
    change Algebra.FinitePresentation X (Fin n → X)
    infer_instance
  have hB : Algebra.FinitePresentation (G.obj X) B' := by
    change Algebra.FinitePresentation X (X ⊗[R] B)
    infer_instance
  letI : Algebra L (A ⊗[X] L) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra L (B' ⊗[X] L) := Algebra.TensorProduct.rightAlgebra
  let commA : A ⊗[X] L ≃ₐ[L] L ⊗[X] A :=
    { Algebra.TensorProduct.comm X A L with
      commutes' := fun r ↦ by
        change Algebra.TensorProduct.comm X A L (1 ⊗ₜ[X] r) = r ⊗ₜ[X] 1
        rfl }
  let splitA : L ⊗[X] A ≃ₐ[L] (Fin n → L) :=
    (Algebra.TensorProduct.piRight X L L (fun _ : Fin n ↦ X)).trans
      (AlgEquiv.piCongrRight fun _ ↦ Algebra.TensorProduct.rid X L L)
  let commB : B' ⊗[X] L ≃ₐ[L] L ⊗[X] B' :=
    { Algebra.TensorProduct.comm X B' L with
      commutes' := fun r ↦ by
        change Algebra.TensorProduct.comm X B' L (1 ⊗ₜ[X] r) = r ⊗ₜ[X] 1
        rfl }
  let cancelB : L ⊗[X] B' ≃ₐ[L] L ⊗[R] B :=
    Algebra.TensorProduct.cancelBaseChange R X L L B
  let limitEquiv : A ⊗[X] L ≃ₐ[L] B' ⊗[X] L :=
    (commA.trans splitA).trans ((commB.trans cancelB).trans hstrictEquiv).symm
  let limitEquiv' : LimitBaseChange G d X A ≃ₐ[LimitRing G d X]
      LimitBaseChange G d X B' := by
    change A ⊗[X] L ≃ₐ[L] B' ⊗[X] L
    exact limitEquiv
  obtain ⟨P⟩ := exists_descendedAlgEquiv G d hd X A B' hA hB limitEquiv'
  let Y := P.stage
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
  let commStageA : StageBaseChange G X A Y ≃ₐ[T] T ⊗[X] A :=
    { Algebra.TensorProduct.comm X A T with
      commutes' := fun r ↦ by
        change Algebra.TensorProduct.comm X A T (1 ⊗ₜ[X] r) = r ⊗ₜ[X] 1
        rfl }
  let splitStage : T ⊗[X] A ≃ₐ[T] (Fin n → T) :=
    (Algebra.TensorProduct.piRight X T T (fun _ : Fin n ↦ X)).trans
      (AlgEquiv.piCongrRight fun _ ↦ Algebra.TensorProduct.rid X T T)
  let commStageB : StageBaseChange G X B' Y ≃ₐ[T] T ⊗[X] B' :=
    { Algebra.TensorProduct.comm X B' T with
      commutes' := fun r ↦ by
        change Algebra.TensorProduct.comm X B' T (1 ⊗ₜ[X] r) = r ⊗ₜ[X] 1
        rfl }
  let cancelStage : T ⊗[X] B' ≃ₐ[T] T ⊗[R] B :=
    Algebra.TensorProduct.cancelBaseChange R X T T B
  let final : T ⊗[R] B ≃ₐ[T] (Fin n → T) :=
    ((commStageB.trans cancelStage).symm.trans P.equiv.symm).trans
      (commStageA.trans splitStage)
  -- the stage lies over `y`
  let Z : PointedEtaleNeighborhood R Ω := Y.right
  let y' : PrimeSpectrum Z :=
    ⟨RingHom.ker Z.point.toRingHom, RingHom.ker_isPrime Z.point.toRingHom⟩
  have hy' : y'.asIdeal.under R = y.asIdeal := by
    change (RingHom.ker Z.point.toRingHom).under R = y.asIdeal
    ext r
    have h := SetLike.ext_iff.mp hΩ r
    rw [RingHom.mem_ker] at h
    simp only [Ideal.mem_under, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, Z.point.commutes]
    exact h
  let _ : IsNoetherianRing Z := Algebra.FiniteType.isNoetherianRing R Z
  refine ⟨Z, inferInstance, inferInstance, inferInstance, ⟨y', hy'⟩, inferInstance, n, ?_⟩
  exact ⟨final⟩

#print axioms isFiniteSplit_of_strictlyHenselianLocalRing
#print axioms strictlyHenselianLocalRing_of_ringEquiv
#print axioms localColimit_strictlyHenselianLocalRing_of_prime
#print axioms hasSplitCoverAt_of_finite_etale

end Pcf.Stacks.SchemeLevel
