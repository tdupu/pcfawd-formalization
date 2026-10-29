/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Vendor.RegularLocalization.AuslanderBuchsbaumSerre
public import Pcf.Vendor.RegularLocalization.RegularGlobalDimension
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension

/-!
# Regularity descends along finite free local extensions

If `A` is a Noetherian local ring and `B` is a finite free `A`-algebra which is
a regular local ring, then `A` is regular. Projective `B`-modules are
projective over `A`, so projective dimension does not increase under
restriction of scalars, and the `A`-module `m_A` is an `A`-direct summand of
`B ⊗_A m_A`. This is the finite free case of flat descent of regularity (Stacks Lemma
10.164.4); no Tor or Ext base change is used.
-/

@[expose] public section

namespace Pcf

open CategoryTheory

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B]

/-- Projective `B`-modules are projective over `A` when `B` is free over `A`. -/
theorem Module.Projective.of_free_algebra (P : Type u) [AddCommGroup P] [Module B P]
    [Module A P] [IsScalarTower A B P] [Module.Projective B P] : Module.Projective A P := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective B P›
  have bB := Module.Free.chooseBasis A B
  have : Module.Free A (P →₀ B) :=
    .of_basis (bB.smulTower (Finsupp.basisSingleOne (R := B) (ι := P)))
  refine Module.Projective.of_split (s.restrictScalars A)
    ((Finsupp.linearCombination B id).restrictScalars A) ?_
  ext x
  exact LinearMap.congr_fun hs x

instance restrictScalars_preservesProjective :
    (ModuleCat.restrictScalars.{u} (algebraMap A B)).PreservesProjectiveObjects where
  projective_obj X {proj} := by
    rw [← IsProjective.iff_projective] at proj ⊢
    let : Module A X := Module.compHom X (algebraMap A B)
    have : IsScalarTower A B X := ⟨fun a b x ↦ by
      rw [Algebra.smul_def, mul_smul]; rfl⟩
    exact Module.Projective.of_free_algebra (A := A) (B := B) X

open Limits in
theorem hasProjectiveDimensionLE_restrictScalars (n : ℕ) (M : ModuleCat.{u} B)
    [HasProjectiveDimensionLE M n] :
    HasProjectiveDimensionLE ((ModuleCat.restrictScalars.{u} (algebraMap A B)).obj M) n := by
  induction n generalizing M with
  | zero =>
    have projle : HasProjectiveDimensionLE M 0 := ‹_›
    simp only [HasProjectiveDimensionLE, zero_add] at projle ⊢
    rw [← projective_iff_hasProjectiveDimensionLT_one] at projle ⊢
    exact (ModuleCat.restrictScalars.{u} (algebraMap A B)).projective_obj M
  | succ n ih =>
    rcases ModuleCat.enoughProjectives.1 M with ⟨⟨P, f⟩⟩
    let T := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
    have T_exact : T.ShortExact := { exact := ShortComplex.exact_kernel f }
    let TS := T.map (ModuleCat.restrictScalars.{u} (algebraMap A B))
    have TS_exact : TS.ShortExact :=
      T_exact.map_of_exact (ModuleCat.restrictScalars.{u} (algebraMap A B))
    have : Projective TS.X₂ := (ModuleCat.restrictScalars.{u} (algebraMap A B)).projective_obj _
    have := (T_exact.hasProjectiveDimensionLT_X₃_iff n ‹_›).mp ‹_›
    exact (TS_exact.hasProjectiveDimensionLT_X₃_iff n ‹_›).mpr (ih (kernel f))

open IsLocalRing TensorProduct in
/-- Stacks Lemma 10.110.9 for a finite free extension: if `B` is finite free over the
Noetherian local ring `A` and `B` is a regular local ring, then `A` is regular.

Divergence from Stacks: Stacks assumes only that `A → B` is a flat local
homomorphism of Noetherian local rings; here `B` is finite free over `A`. -/
@[stacks 00OF "finite free extensions"]
theorem isRegularLocalRing_of_free_of_isRegularLocalRing
    [IsLocalRing A] [IsNoetherianRing A] [Module.Finite A B]
    [IsRegularLocalRing B] : IsRegularLocalRing A := by
  classical
  apply Pcf.Vendor.IsRegularLocalRing.of_maximalIdeal_hasProjectiveDimensionLE.{u}
  set M := Shrink.{u} (maximalIdeal A)
  let N := B ⊗[A] M
  have : Module.Finite A M := Module.Finite.equiv (Shrink.linearEquiv A (maximalIdeal A)).symm
  have : Module.Finite B N := inferInstance
  obtain ⟨n, hn⟩ : ∃ n, HasProjectiveDimensionLE (ModuleCat.of B N) n := by
    have := Pcf.Vendor.projectiveDimension_ne_top_of_isRegularLocalRing.{u} (ModuleCat.of B N)
    rw [projectiveDimension_ne_top_iff] at this
    exact this
  have hres := hasProjectiveDimensionLE_restrictScalars (A := A) n (ModuleCat.of B N)
  refine ⟨n, ?_⟩
  set Y := (ModuleCat.restrictScalars.{u} (algebraMap A B)).obj (ModuleCat.of B N)
  let b := Module.Free.chooseBasis A B
  obtain ⟨i₀⟩ := b.index_nonempty
  let ι : M →ₗ[A] N := (TensorProduct.mk A B M) (b i₀)
  let ρ : N →ₗ[A] M := TensorProduct.lid A M ∘ₗ (b.coord i₀).rTensor M
  have hρι : ∀ m, ρ (ι m) = m := by
    intro m
    change TensorProduct.lid A M ((b.coord i₀).rTensor M (b i₀ ⊗ₜ m)) = m
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
    simp
  have hsmul : ∀ (a : A) (y : N), (algebraMap A B a) • y = a • y := fun a y ↦ algebraMap_smul B a y
  let ι' : ModuleCat.of A M ⟶ Y := ModuleCat.ofHom (X := ModuleCat.of A M) (Y := Y)
    { toFun := ι, map_add' := ι.map_add,
      map_smul' := fun a m ↦ by
        exact (map_smul ι a m).trans (hsmul a (ι m)).symm }
  let ρ' : Y ⟶ ModuleCat.of A M := ModuleCat.ofHom (X := Y) (Y := ModuleCat.of A M)
    { toFun := ρ, map_add' := ρ.map_add,
      map_smul' := fun a y ↦ by
        exact (congrArg ρ (hsmul a (show N from y))).trans (ρ.map_smul a (show N from y)) }
  let r : Retract (ModuleCat.of A M) Y := ⟨ι', ρ', by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact hρι⟩
  exact r.hasProjectiveDimensionLT (n + 1)

#print axioms isRegularLocalRing_of_free_of_isRegularLocalRing

#print axioms Module.Projective.of_free_algebra
#print axioms hasProjectiveDimensionLE_restrictScalars

end Pcf
