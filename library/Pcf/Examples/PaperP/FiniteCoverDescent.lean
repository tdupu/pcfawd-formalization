/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Adjoin.Tower

/-!
# Descending "finite type" and "separated" along a finite cover

For `paper-p.tex`, Example `ex:monodromy-loss` (l. 846–868): the pinched `X` is a variety. Both
properties are descended from `E ×ₖ ℙ¹` along the finite surjective `ν : E ×ₖ ℙ¹ → X`.

* `locallyOfFiniteType_of_finite_cover` (Artin–Tate, Stacks `00IS`): if `ν : Y → X` is finite and
  scheme-theoretically dominant, `S` is locally Noetherian, and `ν ≫ f` is locally of finite type,
  then so is `f : X → S`. On affine opens `Γ(X, V) ⊂ Γ(Y, ν⁻¹V)` is a module-finite subring of an
  algebra of finite type over the Noetherian `Γ(S, U)`.
* `isSeparated_of_surjective_universallyClosed` (Stacks `09MQ`): if `ν : Y → X` is surjective and
  universally closed and `ν ≫ f` is separated, then so is `f`. The diagonal of `f` is an immersion
  whose image is the image of the (closed) diagonal of `ν ≫ f` under the closed map `ν ×_S ν`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace Pcf.Examples.PaperP.FiniteCoverDescent

universe u

set_option linter.style.haveILetI false

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (ν : Y ⟶ X)

/-- **Finite type descends along a finite scheme-theoretically dominant cover** (Artin–Tate). -/
theorem locallyOfFiniteType_of_finite_cover [IsFinite ν] [IsSchemeTheoreticallyDominant ν]
    [IsLocallyNoetherian S] [LocallyOfFiniteType (ν ≫ f)] : LocallyOfFiniteType f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyOfFiniteType)]
  intro U V e
  have hV' : IsAffineOpen (ν ⁻¹ᵁ (V : X.Opens)) := V.2.preimage ν
  have h1 : (f.appLE U V e ≫ ν.app V).hom.FiniteType := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    exact HasRingHomProperty.appLE (P := @LocallyOfFiniteType) (ν ≫ f) ‹_› U ⟨_, hV'⟩ _
  have h2 : (ν.app V).hom.Finite := ν.finite_app V V.2
  have h3 : Function.Injective (ν.app V) := ν.app_injective V
  have hN : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian U
  letI : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V e).hom.toAlgebra
  letI : Algebra Γ(X, V) Γ(Y, ν ⁻¹ᵁ V) := (ν.app V).hom.toAlgebra
  letI : Algebra Γ(S, U) Γ(Y, ν ⁻¹ᵁ V) := ((ν.app V).hom.comp (f.appLE U V e).hom).toAlgebra
  haveI : IsScalarTower Γ(S, U) Γ(X, V) Γ(Y, ν ⁻¹ᵁ V) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hAC : (⊤ : Subalgebra Γ(S, U) Γ(Y, ν ⁻¹ᵁ V)).FG := by
    have : ((ν.app V).hom.comp (f.appLE U V e).hom).FiniteType := h1
    exact this.out
  have hBC : (⊤ : Submodule Γ(X, V) Γ(Y, ν ⁻¹ᵁ V)).FG := h2.fg_top
  exact ⟨fg_of_fg_of_fg _ _ _ hAC hBC h3⟩

/-- **Separatedness descends along a surjective universally closed cover** (Stacks `09MQ`). -/
theorem isSeparated_of_surjective_universallyClosed [Surjective ν] [UniversallyClosed ν]
    [IsSeparated (ν ≫ f)] : IsSeparated f := by
  let g := ν ≫ f
  let M : pullback g g ⟶ pullback f f :=
    pullback.map g g f f ν ν (𝟙 S) (by simp [g]) (by simp [g])
  have hM : UniversallyClosed M :=
    MorphismProperty.pullbackMap (P := @UniversallyClosed) (f := g) (g := g) (f' := f) (g' := f)
      (i₁ := ν) (i₂ := ν) ‹_› ‹_› rfl rfl
  have hcomm : pullback.diagonal g ≫ M = ν ≫ pullback.diagonal f := by
    apply pullback.hom_ext <;> simp [M]
  have hrange : Set.range (pullback.diagonal f) = M '' Set.range (pullback.diagonal g) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, rfl⟩ := ν.surjective x
      refine ⟨pullback.diagonal g y, ⟨y, rfl⟩, ?_⟩
      rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨ν y, by rw [← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply]⟩
  have hclosed : IsClosed (Set.range (pullback.diagonal f)) := by
    rw [hrange]
    exact M.isClosedMap _ (pullback.diagonal g).isClosedEmbedding.isClosed_range
  exact ⟨.of_isPreimmersion _ hclosed⟩

end Pcf.Examples.PaperP.FiniteCoverDescent

#print axioms Pcf.Examples.PaperP.FiniteCoverDescent.locallyOfFiniteType_of_finite_cover
#print axioms Pcf.Examples.PaperP.FiniteCoverDescent.isSeparated_of_surjective_universallyClosed
