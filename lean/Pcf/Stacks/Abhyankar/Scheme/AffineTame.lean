/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.Scheme.AffineTameTransfer
public import Pcf.Stacks.Abhyankar.StandardCoverGeometry
public import Pcf.Stacks.Abhyankar.StrictHenselizationStandardDescent
public import Mathlib.RingTheory.Localization.Pi

/-!
# The affine `0EYG` statement at a point of the divisor, from the affine hypothesis

Main theorem: `Pcf.Stacks.SchemeLevel.hasLocalizedStandardCoverAt_of_tame`.  Given the affine
hypothesis `AbhyankarLemmaTameOfFinite` at the local ring `R_y`
(`Pcf.Stacks.abhyankarLemmaTameOfFinite`, or the characteristic-zero
`Pcf.Stacks.abhyankarLemmaOfFinite`), a finite étale `R_a`-algebra `B` which is tame in
codimension one along `V(a)` admits, at every `y ∈ V(a)`, a pointed étale
neighbourhood `R → A` with `A ⊗_R B ≅ ∏_i A_a[x]/(x^{e_i} - u_i a)`
(`HasLocalizedStandardCoverAt`).

## Stacks proof step → Lean lemma (proof of Lemma 58.31.5, Tag `0EYG`)

* Shrink to `X = Spec A`, `D = V(f)`, `Y = Spec B`: the statement itself (the affine chart is
  chosen at the scheme level).
* Reduce to the strict henselization of `𝒪_{X,x}`: replaced.  The hypothesis is applied at `R_y`
  (`hasAbhyankarStandardCoverAt_ny`), and the resulting étale neighbourhood is mapped into the
  colimit `L` of pointed étale neighbourhoods (`nonempty_localizedStandard_of_algHom`, using the
  Stacks `04GW` comparison `localColimitAtPrimeRingEquiv`).
* `A^{sh}/fA^{sh}` regular and base change keeps tameness (Lemma 58.31.1, Tag `0EYD`): replaced
  by a localization argument, `isTamelyRamifiedInCodimensionOneAlong_ny` (Mathlib's localization
  invariance of ramification indices).
* Strictly henselian case `A^{sh} ⊗_A B ≅ ∏ A^{sh}_f[x]/(x^{e_i} - f)`: the affine hypothesis
  `AbhyankarLemmaTameOfFinite` (`Pcf.Stacks.abhyankarLemmaTameOfFinite`).
* Descend the isomorphism to some `A_λ` (Algebra, Lemma 10.127.8, Tag `05N9`) and make the `e_i`
  invertible: `exists_stage_localizedStandard`, `exists_stage_isUnit_natCast` (built on pcf's
  `exists_descendedAlgEquiv`).
* `Spec(A_λ) → Spec(A)` is the required étale neighbourhood: `hasLocalizedStandardCoverAt_of_stage`.

The differences in the second and third steps are forced by the shape of the affine hypothesis: like
the characteristic-zero `Pcf.Stacks.AbhyankarLemmaOfFinite`, it is stated for the finite
normalization `S` of `R` in `S[1/a]`, whose finiteness over `R` is not available before this
theorem; over the regular local ring `R_y` it is (Stacks Tag `032L`, `finite_ny`).  The finiteness
over `R` itself (first assertion of `0EYH`) is then deduced from this theorem and
`integralClosure_finite` (`Pcf.Stacks.finite_of_isIntegralClosure_away`,
`Pcf.Stacks.Abhyankar.FiniteNormalization`).
-/

@[expose] public section

universe u

open TensorProduct IsLocalRing Algebra

set_option linter.style.haveILetI false

namespace Pcf.Stacks.SchemeLevel

namespace AffineTame

open Pcf.Stacks.PointedEtaleNeighborhood

/-- `∏_j T[x]/(x^{e_j} - v_j a)`. -/
abbrev StdC (T : Type u) [CommRing T] {ι : Type} (v : ι → Tˣ) (a : T) (e : ι → ℕ) :
    Type u :=
  ∀ j, AdjoinRoot (Pcf.LocalModel.localPoly (v j) a (e j))

/-- `(∏_j T[x]/(x^{e_j} - v_j a))[1/a]`. -/
abbrev LocStdC (T : Type u) [CommRing T] {ι : Type} (v : ι → Tˣ) (a : T) (e : ι → ℕ) :
    Type u :=
  Localization.Away (algebraMap T (StdC T v a e) a)

/-- Base change of `(∏_j T[x]/(x^{e_j} - v_j a))[1/a]` along `T → T'`. -/
noncomputable def locStdCBaseChange {T T' : Type u} [CommRing T] [CommRing T'] [Algebra T T']
    {ι : Type} [Fintype ι] (v : ι → Tˣ) (v' : ι → T'ˣ)
    (hv : ∀ j, Units.map (algebraMap T T') (v j) = v' j) (a : T) (a' : T')
    (ha : algebraMap T T' a = a') (e : ι → ℕ) :
    T' ⊗[T] LocStdC T v a e ≃ₐ[T'] LocStdC T' v' a' e :=
  let c : StdC T v a e := algebraMap T (StdC T v a e) a
  let F : T' ⊗[T] StdC T v a e ≃ₐ[T'] StdC T' v' a' e :=
    (standardCoversBaseChangeEquivOfUnitEq ι v v' hv a e).trans
      (AlgEquiv.piCongrRight fun j ↦ AdjoinRoot.algEquivOfEq T' _ _ (by rw [ha]))
  have hF : F ((1 : T') ⊗ₜ[T] c) = algebraMap T' (StdC T' v' a' e) a' := by
    have : (1 : T') ⊗ₜ[T] c = algebraMap T' (T' ⊗[T] StdC T v a e) a' := by
      rw [← ha]
      change (1 : T') ⊗ₜ[T] algebraMap T (StdC T v a e) a = _
      rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
      rfl
    rw [this, AlgEquiv.commutes]
  (IsLocalization.Away.tensorProductEquivTMulRight T T' c (LocStdC T v a e)).trans
    (IsLocalization.algEquivOfAlgEquiv (M := Submonoid.powers ((1 : T') ⊗ₜ[T] c))
      (T := Submonoid.powers (algebraMap T' (StdC T' v' a' e) a'))
      _ _ F (by rw [Submonoid.map_powers]; exact congrArg Submonoid.powers hF))

variable {R : Type u} [CommRing R] (a : R) (Ra : Type u) [CommRing Ra] [Algebra R Ra]
  [IsLocalization.Away a Ra]
  (B : Type u) [CommRing B] [Algebra Ra B] [Algebra R B] [IsScalarTower R Ra B]
  (y : Ideal R) [y.IsPrime]

/-- A point `R'' → κ(y'')` over `R_y` for an étale neighbourhood of the closed point. -/
theorem ker_residueField {R'' : Type u} [CommRing R''] [Algebra (Localization.AtPrime y) R'']
    (y'' : Ideal R'') [y''.IsPrime]
    (hy'' : y''.under (Localization.AtPrime y) = maximalIdeal (Localization.AtPrime y)) :
    letI : Algebra R y''.ResidueField := ((algebraMap R'' y''.ResidueField).comp
      ((algebraMap (Localization.AtPrime y) R'').comp
        (algebraMap R (Localization.AtPrime y)))).toAlgebra
    RingHom.ker (algebraMap R y''.ResidueField) = y := by
  letI : Algebra R y''.ResidueField := ((algebraMap R'' y''.ResidueField).comp
      ((algebraMap (Localization.AtPrime y) R'').comp
        (algebraMap R (Localization.AtPrime y)))).toAlgebra
  ext r
  rw [RingHom.mem_ker, RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
    Ideal.algebraMap_residueField_eq_zero]
  change algebraMap R (Localization.AtPrime y) r ∈ y''.under (Localization.AtPrime y) ↔ _
  rw [hy'', ← Ideal.mem_comap, ← Ideal.under_def,
    IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime y) y]

include Ra in
/-- From a standard presentation of `R'' ⊗_{R_y} N_y` over an `R_y`-algebra `R''`, and an
`R_y`-algebra map `R'' → L`, a localized standard presentation of `L ⊗_R B`. -/
theorem nonempty_localizedStandard_of_algHom [Module.Finite Ra B]
    {L : Type u} [CommRing L] [Algebra (Localization.AtPrime y) L] [Algebra R L]
    [IsScalarTower R (Localization.AtPrime y) L]
    {R'' : Type u} [CommRing R''] [Algebra (Localization.AtPrime y) R'']
    (ψ : R'' →ₐ[Localization.AtPrime y] L)
    {ι : Type} [Finite ι] (e : ι → ℕ) (u : ι → R''ˣ)
    (F0 : R'' ⊗[Localization.AtPrime y] Ny B y ≃ₐ[R'']
      ∀ j, AdjoinRoot (Pcf.LocalModel.localPoly (u j)
        (algebraMap (Localization.AtPrime y) R'' (ay a y)) (e j))) :
    Nonempty (L ⊗[R] B ≃ₐ[L]
      LocStdC L (fun j ↦ Units.map ψ.toRingHom.toMonoidHom (u j)) (algebraMap R L a) e) := by
  letI := Fintype.ofFinite ι
  set Ry := Localization.AtPrime y
  letI : Algebra R'' L := ψ.toRingHom.toAlgebra
  haveI : IsScalarTower Ry R'' L := IsScalarTower.of_algebraMap_eq fun r ↦ (ψ.commutes r).symm
  have hL : algebraMap R'' L (algebraMap Ry R'' (ay a y)) = algebraMap R L a := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  set v : ι → Lˣ := fun j ↦ Units.map ψ.toRingHom.toMonoidHom (u j)
  -- base change of the standard presentation to `L`
  let G : L ⊗[R''] (R'' ⊗[Ry] Ny B y) ≃ₐ[L] StdC L v (algebraMap R L a) e :=
    ((Algebra.TensorProduct.congr AlgEquiv.refl F0).trans
      (standardCoversBaseChangeEquiv ι u (algebraMap Ry R'' (ay a y)) e)).trans
      (AlgEquiv.piCongrRight fun j ↦ AdjoinRoot.algEquivOfEq L _ _ (by rw [hL]; rfl))
  let F1 : L ⊗[Ry] Ny B y ≃ₐ[L] StdC L v (algebraMap R L a) e :=
    (Algebra.TensorProduct.cancelBaseChange Ry R'' L L (Ny B y)).symm.trans G
  -- localize at `a`
  haveI := isLocalization_away_ny a Ra B y
  let g : Ny B y := algebraMap Ry (Ny B y) (ay a y)
  let H1 : L ⊗[Ry] By B y ≃ₐ[L] Localization.Away ((1 : L) ⊗ₜ[Ry] g) :=
    IsLocalization.Away.tensorProductEquivTMulRight Ry L g (By B y)
  have hg : F1 ((1 : L) ⊗ₜ[Ry] g) =
      algebraMap L (StdC L v (algebraMap R L a) e) (algebraMap R L a) := by
    have : (1 : L) ⊗ₜ[Ry] g = algebraMap L (L ⊗[Ry] Ny B y) (algebraMap R L a) := by
      rw [IsScalarTower.algebraMap_apply R Ry L a]
      change (1 : L) ⊗ₜ[Ry] algebraMap Ry (Ny B y) (ay a y) = _
      rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
      rfl
    rw [this, AlgEquiv.commutes]
  let H2 : Localization.Away ((1 : L) ⊗ₜ[Ry] g) ≃ₐ[L] LocStdC L v (algebraMap R L a) e :=
    IsLocalization.algEquivOfAlgEquiv (M := Submonoid.powers ((1 : L) ⊗ₜ[Ry] g))
      (T := Submonoid.powers (algebraMap L (StdC L v (algebraMap R L a) e) (algebraMap R L a)))
      _ _ F1 (by rw [Submonoid.map_powers]; exact congrArg Submonoid.powers hg)
  let H3 : L ⊗[R] B ≃ₐ[L] L ⊗[Ry] By B y :=
    (Algebra.TensorProduct.cancelBaseChange R Ry L L B).symm
  exact ⟨H3.trans (H1.trans H2)⟩

open CategoryTheory Limits in
/-- Finitely many positive integers invertible in the strict local colimit are already invertible
at one pointed étale stage. -/
theorem exists_stage_isUnit_natCast {R Ω : Type u} [CommRing R] [Field Ω] [Algebra R Ω]
    (ι : Type) [Finite ι] (e : ι → ℕ) (he : ∀ j, IsUnit ((e j : ℕ) : LocalColimit R Ω)) :
    ∃ X : PointedEtaleNeighborhood R Ω, ∀ j, IsUnit ((e j : ℕ) : X) := by
  classical
  letI := Fintype.ofFinite ι
  let s : Set (LocalColimit R Ω) :=
    Set.range (fun j : ι ↦ (((he j).unit⁻¹ : (LocalColimit R Ω)ˣ) : LocalColimit R Ω))
  obtain ⟨X, hX⟩ := exists_stage_containing_finite_localColimit_set
    (R := R) (Ω := Ω) s (Set.finite_range _)
  choose y hy using fun j : ι ↦ hX (show (((he j).unit⁻¹ : (LocalColimit R Ω)ˣ) :
    LocalColimit R Ω) ∈ s from ⟨j, rfl⟩)
  let F := functor (R := R) (Ω := Ω)
  let c := (Under.forget (CommRingCat.of R)).mapCocone (localCocone (R := R) (Ω := Ω))
  have hc : IsColimit c :=
    isColimitOfPreserves (Under.forget (CommRingCat.of R))
      (localCoconeIsColimit (R := R) (Ω := Ω))
  have hxy (j : ι) : (c.ι.app X).hom (((e j : ℕ) : X) * y j) = (c.ι.app X).hom 1 := by
    change toLocalColimitAlgHom (R := R) (Ω := Ω) X (((e j : ℕ) : X) * y j) =
      toLocalColimitAlgHom (R := R) (Ω := Ω) X 1
    rw [map_mul, hy j, map_one, map_natCast]
    exact (he j).mul_val_inv
  choose Y f hunit using fun j : ι ↦ (hc.eq_iff' _ 1).mp (hxy j)
  obtain ⟨Z, hZ⟩ := IsFiltered.sup_objs_exists (Finset.univ.image Y)
  have hY (j : ι) : Y j ∈ Finset.univ.image Y :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  let g (j : ι) : Y j ⟶ Z := (hZ (hY j)).some
  refine ⟨Z, fun j ↦ ?_⟩
  have hunit' : (f j).hom (((e j : ℕ) : X) * y j) = (f j).hom 1 := hunit j
  have h1 : (g j).hom ((f j).hom (((e j : ℕ) : X) * y j)) = 1 := by
    rw [hunit', map_one, map_one]
  rw [map_mul, map_mul, map_natCast, map_natCast] at h1
  exact ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

/-- The localized standard covers are finitely presented over a Noetherian base. -/
theorem locStdC_finitePresentation {T : Type u} [CommRing T] [IsNoetherianRing T]
    {ι : Type} [Finite ι] (v : ι → Tˣ) (a : T) (e : ι → ℕ) :
    Algebra.FinitePresentation T (LocStdC T v a e) := by
  letI := Fintype.ofFinite ι
  haveI : Algebra.FinitePresentation (StdC T v a e) (LocStdC T v a e) :=
    IsLocalization.Away.finitePresentation (S := LocStdC T v a e) (algebraMap T (StdC T v a e) a)
  haveI : Algebra.FiniteType T (LocStdC T v a e) :=
    Algebra.FiniteType.trans (S := StdC T v a e) inferInstance inferInstance
  exact Algebra.FinitePresentation.of_finiteType.mp inferInstance

open CategoryTheory Limits Pcf.Stacks.EtaleDescent Pcf.Stacks.EtaleDescent.StageAlgebra
  Pcf.Stacks.EtaleDescent.StageAlgebra.EquivalenceDescent in
/-- **Descent from the strict local colimit (Stacks `05N9`, localized pieces).**  A presentation
`L ⊗_R B ≅ (∏_j L[x]/(x^{e_j} - v_j a))[1/a]` over `L = LocalColimit R Ω` descends to one pointed
étale stage `X`, with the exponents invertible on `X`. -/
theorem exists_stage_localizedStandard {R Ω : Type u} [CommRing R] [Field Ω] [Algebra R Ω]
    [IsNoetherianRing R] (a : R) (B : Type u) [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B] {ι : Type} [Finite ι] (e : ι → ℕ)
    (v : ι → (LocalColimit R Ω)ˣ) (he : ∀ j, IsUnit ((e j : ℕ) : LocalColimit R Ω))
    (E : LocalColimit R Ω ⊗[R] B ≃ₐ[LocalColimit R Ω]
      LocStdC (LocalColimit R Ω) v (algebraMap R (LocalColimit R Ω) a) e) :
    ∃ (X : PointedEtaleNeighborhood R Ω) (vX : ι → Xˣ), (∀ j, IsUnit ((e j : ℕ) : X)) ∧
      Nonempty (X ⊗[R] B ≃ₐ[X] LocStdC X vX (algebraMap R X a) e) := by
  letI := Fintype.ofFinite ι
  classical
  let L := LocalColimit R Ω
  obtain ⟨X0, uX0, huX0⟩ := exists_stage_units ι v
  obtain ⟨X1, hX1⟩ := exists_stage_isUnit_natCast ι e he
  obtain ⟨X, ⟨f0⟩, ⟨f1⟩⟩ := exists_common_refinement X0 X1
  let unitX : ι → Xˣ := fun j ↦ Units.map f0.hom.toRingHom.toMonoidHom (uX0 j)
  have hunitX (j : ι) : Units.map (toLocalColimitAlgHom (R := R) (Ω := Ω) X).toRingHom.toMonoidHom
      (unitX j) = v j := by
    rw [← huX0 j]
    ext
    exact DFunLike.congr_fun (toLocalColimitAlgHom_naturality (R := R) (Ω := Ω) f0) _
  have heX (j : ι) : IsUnit ((e j : ℕ) : X) := by
    simpa only [map_natCast] using (hX1 j).map f1.hom
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
  let A := LocStdC X unitX (algebraMap R X a) e
  let Bs := X ⊗[R] B
  letI : CommRing Bs := by dsimp [Bs]; infer_instance
  letI : Algebra X Bs := Algebra.TensorProduct.leftAlgebra
  letI : IsNoetherianRing X := Algebra.FiniteType.isNoetherianRing R X
  letI : Algebra (G.obj X) A := by change Algebra X A; infer_instance
  letI : Algebra (G.obj X) Bs := by change Algebra X Bs; infer_instance
  letI : IsNoetherianRing (G.obj X) := by change IsNoetherianRing X; infer_instance
  have hA : Algebra.FinitePresentation (G.obj X) A := by
    change Algebra.FinitePresentation X A
    exact locStdC_finitePresentation unitX _ e
  letI : Algebra.FinitePresentation X Bs := Algebra.FinitePresentation.baseChange X
  have hB : Algebra.FinitePresentation (G.obj X) Bs := by
    change Algebra.FinitePresentation X Bs
    infer_instance
  letI : Algebra L (A ⊗[X] L) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra L (Bs ⊗[X] L) := Algebra.TensorProduct.rightAlgebra
  have hunitXL (j : ι) : Units.map (algebraMap X L) (unitX j) = v j := hunitX j
  let commA : A ⊗[X] L ≃ₐ[L] L ⊗[X] A :=
    { Algebra.TensorProduct.comm X A L with
      commutes' := fun r ↦ by
        change Algebra.TensorProduct.comm X A L (1 ⊗ₜ[X] r) = r ⊗ₜ[X] 1
        rfl }
  let bcL : L ⊗[X] A ≃ₐ[L] LocStdC L v (algebraMap R L a) e :=
    locStdCBaseChange unitX v hunitXL (algebraMap R X a) (algebraMap R L a)
      (IsScalarTower.algebraMap_apply R X L a).symm e
  let commB : Bs ⊗[X] L ≃ₐ[L] L ⊗[X] Bs :=
    { Algebra.TensorProduct.comm X Bs L with
      commutes' := fun r ↦ by
        change Algebra.TensorProduct.comm X Bs L (1 ⊗ₜ[X] r) = r ⊗ₜ[X] 1
        rfl }
  let cancelB : L ⊗[X] Bs ≃ₐ[L] L ⊗[R] B :=
    Algebra.TensorProduct.cancelBaseChange R X L L B
  let limitEquiv : A ⊗[X] L ≃ₐ[L] Bs ⊗[X] L :=
    (commA.trans bcL).trans ((commB.trans cancelB).trans E).symm
  let limitEquiv' : LimitBaseChange G d X A ≃ₐ[LimitRing G d X]
      LimitBaseChange G d X Bs := by
    change A ⊗[X] L ≃ₐ[L] Bs ⊗[X] L
    exact limitEquiv
  obtain ⟨P⟩ := exists_descendedAlgEquiv G d hd X A Bs hA hB limitEquiv'
  let T := StageRing G X P.stage
  letI : Algebra X T := by change Algebra (G.obj X) T; infer_instance
  letI : Algebra R T := by change Algebra R P.stage.right; infer_instance
  letI : IsScalarTower R X T :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := X) (A := T) (fun r ↦ by
      change algebraMap R P.stage.right r = P.stage.hom.hom (algebraMap R X r)
      exact (P.stage.hom.hom.commutes r).symm)
  let commStage : StageBaseChange G X Bs P.stage ≃ₐ[T] T ⊗[X] Bs :=
    { Algebra.TensorProduct.comm X Bs T with
      commutes' := fun r ↦ by
        change Algebra.TensorProduct.comm X Bs T (1 ⊗ₜ[X] r) = r ⊗ₜ[X] 1
        rfl }
  let commStageA : StageBaseChange G X A P.stage ≃ₐ[T] T ⊗[X] A :=
    { Algebra.TensorProduct.comm X A T with
      commutes' := fun r ↦ by
        change Algebra.TensorProduct.comm X A T (1 ⊗ₜ[X] r) = r ⊗ₜ[X] 1
        rfl }
  let cancelStage : T ⊗[X] Bs ≃ₐ[T] T ⊗[R] B :=
    Algebra.TensorProduct.cancelBaseChange R X T T B
  let bcT : T ⊗[X] A ≃ₐ[T] LocStdC T (fun j ↦ Units.map (algebraMap X T) (unitX j))
      (algebraMap R T a) e :=
    locStdCBaseChange unitX _ (fun _ ↦ rfl) (algebraMap R X a) (algebraMap R T a)
      (IsScalarTower.algebraMap_apply R X T a).symm e
  refine ⟨P.stage.right, fun j ↦ Units.map (algebraMap X T).toMonoidHom (unitX j),
    fun j ↦ ?_, ?_⟩
  · have h := (heX j).map (algebraMap X T)
    rw [map_natCast] at h
    exact h
  · change Nonempty (T ⊗[R] B ≃ₐ[T] LocStdC T (fun j ↦ Units.map (algebraMap X T) (unitX j))
      (algebraMap R T a) e)
    exact ⟨(((commStage.trans cancelStage).symm.trans P.equiv.symm).trans commStageA).trans bcT⟩
/-- The localization of a finite product of standard covers is the product of the localizations. -/
noncomputable def locStdCPiEquiv {T : Type u} [CommRing T] {ι : Type} [Fintype ι]
    (v : ι → Tˣ) (a : T) (e : ι → ℕ) :
    LocStdC T v a e ≃ₐ[T] ∀ j, Localization.Away
      (algebraMap T (AdjoinRoot (Pcf.LocalModel.localPoly (v j) a (e j))) a) :=
  haveI : IsLocalization (Submonoid.powers (algebraMap T (StdC T v a e) a))
      (∀ j, Localization.Away
        (algebraMap T (AdjoinRoot (Pcf.LocalModel.localPoly (v j) a (e j))) a)) := by
    rw [IsLocalization.iff_map_piEvalRingHom]
    simp only [Submonoid.map_powers]
    change IsLocalization (Submonoid.pi Set.univ fun j ↦ Submonoid.powers
      (algebraMap T (AdjoinRoot (Pcf.LocalModel.localPoly (v j) a (e j))) a)) _
    infer_instance
  (IsLocalization.algEquiv (Submonoid.powers (algebraMap T (StdC T v a e) a))
    (LocStdC T v a e) _).restrictScalars T

/-- Packaging a stage presentation as `HasLocalizedStandardCoverAt`. -/
theorem hasLocalizedStandardCoverAt_of_stage {R Ω : Type u} [CommRing R] [Field Ω]
    [Algebra R Ω] [IsNoetherianRing R] (a : R) (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span {a})] (B : Type u) [CommRing B] [Algebra R B]
    (y : PrimeSpectrum R) (hΩ : RingHom.ker (algebraMap R Ω) = y.asIdeal)
    (X : PointedEtaleNeighborhood R Ω) {ι : Type} [Finite ι] (e : ι → ℕ) (he0 : ∀ j, e j ≠ 0)
    (vX : ι → Xˣ) (heX : ∀ j, IsUnit ((e j : ℕ) : X))
    (E : X ⊗[R] B ≃ₐ[X] LocStdC X vX (algebraMap R X a) e) :
    HasLocalizedStandardCoverAt a B y := by
  letI := Fintype.ofFinite ι
  classical
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
  let σ := Fintype.equivFin ι
  refine ⟨X, inferInstance, inferInstance, inferInstance, ⟨y', hy'⟩, inferInstance,
    hmapRegular, inferInstance, Fintype.card ι, fun k ↦ e (σ.symm k), fun k ↦ vX (σ.symm k),
    fun k ↦ Nat.one_le_iff_ne_zero.mpr (he0 _), fun k ↦ heX _, ⟨?_⟩⟩
  exact ((E.trans (locStdCPiEquiv vX (algebraMap R X a) e)).trans
    (standardCoversLocalizationEquiv vX (algebraMap R X a) e)).trans
    (AlgEquiv.piCongrLeft' X _ σ)

end AffineTame

open AffineTame PointedEtaleNeighborhood in
/-- **Affine form of Stacks Lemma 58.31.5 (Tag `0EYG`) at a point of the divisor, from the
affine hypothesis `AbhyankarLemmaTameOfFinite`.**

`R` Noetherian, `a` a nonzerodivisor with `R/(a)` regular (`D = V(a)` an effective Cartier
divisor which is a regular scheme), `B` finite étale over `R_a` (`Y = Spec B → Spec R_a`),
tamely ramified in codimension one along `V(a)` (`ChartTame`), and `y ∈ V(a)`: there is a pointed
étale neighbourhood `R → A` of `y`, `A` Noetherian, `a` a nonzerodivisor of `A` with `A/(a)`
regular, and `A ⊗_R B ≅ ∏_i A_a[x]/(x^{e_i} - u_i a)` with `e_i ≥ 1` invertible in `A`.

The affine hypothesis is used only at the local ring `R_y` (argument `hA`).

Proof route, compared with the proof of Tag `0EYG`:
* Stacks reduces to the strict henselization and proves the strictly henselian case directly.
  Here that case is replaced by the affine hypothesis, applied at `R_y` to the normalization
  `N_y` of `R_y` in `R_y ⊗_R B` (`hasAbhyankarStandardCoverAt_ny`).  This needs `N_y` finite
  (Stacks Tag `032L`, via `finite_ny`), étale away from `a`, the integral closure of `R_y` in
  `N_y[1/a]`, and tame along `V(a)` (`isTamelyRamifiedInCodimensionOneAlong_ny`, a localization
  argument replacing Stacks' Lemma 58.31.1, Tag `0EYD`, which is not needed for a localization).
* The resulting étale neighbourhood `R''` of the closed point of `R_y` is mapped into the colimit
  `L` of pointed étale neighbourhoods of `R` at the residue field `Ω = κ(y'')` of a point of `R''`
  over `y` (Stacks `04GW` comparison `localColimitAtPrimeRingEquiv`, used for an arbitrary field
  `Ω` with kernel `y`, not the separable closure), giving `L ⊗_R B ≅ (∏ L[x]/(x^{e_i}-u_i a))[1/a]`
  (`nonempty_localizedStandard_of_algHom`).
* This presentation descends to one pointed étale stage, as in Stacks via Algebra, Lemma
  10.127.8 (Tag `05N9`, `exists_stage_localizedStandard`), including the invertibility of the
  `e_i` (`exists_stage_isUnit_natCast`). -/
theorem hasLocalizedStandardCoverAt_of_tame
    {R : Type u} [CommRing R] [IsNoetherianRing R] (a : R) (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span {a})]
    (Ra : Type u) [CommRing Ra] [Algebra R Ra] [IsLocalization.Away a Ra]
    (B : Type u) [CommRing B] [Algebra Ra B] [Algebra R B] [IsScalarTower R Ra B]
    [Module.Finite Ra B] [Algebra.Etale Ra B]
    (htame : ChartTame a B) (y : PrimeSpectrum R) (hy : a ∈ y.asIdeal)
    (hA : ∀ (S : Type u) [CommRing S] [Algebra (Localization.AtPrime y.asIdeal) S]
      (b : Localization.AtPrime y.asIdeal),
        AbhyankarLemmaTameOfFinite (Localization.AtPrime y.asIdeal) S b) :
    HasLocalizedStandardCoverAt a B y := by
  obtain ⟨R'', _, _, _, ⟨y'', hy''⟩, _, _, _, ι, _, e, u, he, heU, ⟨F0⟩⟩ :=
    hasAbhyankarStandardCoverAt_ny a Ra B y.asIdeal ha htame hy hA
  set Ry := Localization.AtPrime y.asIdeal
  let Ω := y''.asIdeal.ResidueField
  letI : Algebra R Ω :=
    ((algebraMap R'' Ω).comp ((algebraMap Ry R'').comp (algebraMap R Ry))).toAlgebra
  have hΩ : RingHom.ker (algebraMap R Ω) = y.asIdeal :=
    ker_residueField y.asIdeal y''.asIdeal hy''
  letI : Algebra Ry Ω := atPrimeAlgebra y.asIdeal hΩ
  haveI := atPrimeAlgebra_isScalarTower y.asIdeal hΩ
  have hpt : (algebraMap R'' Ω).comp (algebraMap Ry R'') = algebraMap Ry Ω := by
    apply IsLocalization.ringHom_ext y.asIdeal.primeCompl
    ext r
    exact IsScalarTower.algebraMap_apply R Ry Ω r
  let pt : R'' →ₐ[Ry] Ω :=
    { algebraMap R'' Ω with commutes' := fun r ↦ DFunLike.congr_fun hpt r }
  let X'' := ofEtaleAlgebra (R := Ry) (Ω := Ω) R'' pt
  let ψ' : R'' →ₐ[Ry] LocalColimit Ry Ω :=
    (toLocalColimitAlgHom (R := Ry) (Ω := Ω) X'').comp (ofEtaleAlgebraEquiv R'' pt).symm.toAlgHom
  let φ := localColimitAtPrimeRingEquiv (Ω := Ω) y.asIdeal hΩ
  letI : Algebra Ry (LocalColimit R Ω) :=
    (φ.symm.toRingHom.comp (algebraMap Ry (LocalColimit Ry Ω))).toAlgebra
  haveI : IsScalarTower R Ry (LocalColimit R Ω) := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R (LocalColimit R Ω) r =
      φ.symm (algebraMap Ry (LocalColimit Ry Ω) (algebraMap R Ry r))
    rw [← localColimitAtPrimeRingEquiv_algebraMap, RingEquiv.symm_apply_apply]
  let ψ : R'' →ₐ[Ry] LocalColimit R Ω :=
    { toRingHom := φ.symm.toRingHom.comp ψ'.toRingHom
      commutes' := fun r ↦ by
        change φ.symm (ψ' (algebraMap Ry R'' r)) = φ.symm (algebraMap Ry (LocalColimit Ry Ω) r)
        rw [ψ'.commutes] }
  obtain ⟨E⟩ := nonempty_localizedStandard_of_algHom a Ra B y.asIdeal ψ e u F0
  have heL : ∀ j, IsUnit ((e j : ℕ) : LocalColimit R Ω) := fun j ↦ by
    simpa only [map_natCast] using (heU j).map ψ
  haveI : Algebra.FinitePresentation R Ra := IsLocalization.Away.finitePresentation a
  haveI : Algebra.FinitePresentation R B := Algebra.FinitePresentation.trans R Ra B
  obtain ⟨X, vX, heX, ⟨EX⟩⟩ := exists_stage_localizedStandard a B e _ heL E
  exact hasLocalizedStandardCoverAt_of_stage a ha B y hΩ X e he vX heX EX

end Pcf.Stacks.SchemeLevel
