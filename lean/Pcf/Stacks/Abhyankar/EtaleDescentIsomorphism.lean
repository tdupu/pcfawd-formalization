/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.Algebra.Category.Ring.Under.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Filtered.Final
public import Pcf.Stacks.Abhyankar.EtaleDescentObjects
public import Pcf.Stacks.Abhyankar.StandardCoverPresentation

/-!
# Coherent finite-stage descent of algebra isomorphisms

This file supplies the varying-base-change diagrams needed to use Stacks Tag `05N9` for
isomorphisms.  If `R = colim R_j` and `A_i` is an algebra over one stage `R_i`, the objects

`A_i ⊗[R_i] R_j`, for arrows `i ⟶ j`,

form a filtered diagram whose colimit is `A_i ⊗[R_i] R`.  Applying the map and equality
clauses of `05N9` to two such diagrams descends an isomorphism and its two inverse identities
to one common finite stage.

The final theorem specializes the finite-presentation hypothesis to the finite disjoint union
of standard tame covers occurring in Stacks Tags `0EYG` and `0EYH`.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace Pcf.Stacks.EtaleDescent

variable {J : Type u} [SmallCategory J]

section BaseChangeDiagram

variable (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)

/-- The diagram of `R_i`-algebras `R_j`, indexed by arrows `i ⟶ j`. -/
noncomputable def ringDiagramAbove (i : J) : Under i ⥤ Under (F.obj i) :=
  Under.lift (Under.forget i ⋙ F)
    { app := fun X ↦ F.map X.hom
      naturality := fun X Y f ↦ by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
          Functor.comp_map, Under.forget_map]
        exact (F.congr_map (Under.w f).symm).trans (F.map_comp X.hom f.right) }

/-- The canonical colimit cocone of the rings above `i`, regarded as `R_i`-algebras. -/
noncomputable def ringCoconeAbove (i : J) : Cocone (ringDiagramAbove F i) :=
  Under.liftCocone (Under.forget i ⋙ F)
    { app := fun X ↦ F.map X.hom
      naturality := fun X Y f ↦ by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
          Functor.comp_map, Under.forget_map]
        exact (F.congr_map (Under.w f).symm).trans (F.map_comp X.hom f.right) }
    (c.whisker (Under.forget i)) (c.ι.app i) fun X ↦ by
      change F.map X.hom ≫ c.ι.app X.right = c.ι.app i
      exact c.w X.hom

/-- The cocone `ringCoconeAbove` is colimiting.  This is where filteredness is used: the
forgetful functor from the under-category of `i` is final. -/
noncomputable def ringCoconeAboveIsColimit (i : J) [IsFiltered J] :
    IsColimit (ringCoconeAbove F c i) := by
  letI : Nonempty (Under i) := ⟨Under.mk (𝟙 i)⟩
  apply Under.isColimitLiftCocone
  exact (Functor.Final.isColimitWhiskerEquiv (Under.forget i) c).symm hc

/-- Base change of a fixed `R_i`-algebra along all arrows out of `i`.  The tensor factors are
written as `A_i ⊗[R_i] R_j`; commutativity identifies this with the usual `R_j ⊗[R_i] A_i`. -/
noncomputable def baseChangeDiagram (i : J) (A : Type u) [CommRing A]
    [Algebra (F.obj i) A] : Under i ⥤ CommRingCat.{u} :=
  ringDiagramAbove F i ⋙
    CommRingCat.tensorProd (F.obj i) (CommRingCat.of A) ⋙
    Under.forget (CommRingCat.of A)

/-- The canonical cocone from the varying base changes to `A_i ⊗[R_i] R`. -/
noncomputable def baseChangeCocone (i : J) (A : Type u) [CommRing A]
    [Algebra (F.obj i) A] : Cocone (baseChangeDiagram F i A) :=
  (Under.forget (CommRingCat.of A)).mapCocone
    ((CommRingCat.tensorProd (F.obj i) (CommRingCat.of A)).mapCocone
      (ringCoconeAbove F c i))

/-- Tensor base change commutes with the filtered colimit above a fixed stage. -/
noncomputable def baseChangeCoconeIsColimit (i : J) (A : Type u) [CommRing A]
    [Algebra (F.obj i) A] [IsFiltered J] : IsColimit (baseChangeCocone F c i A) := by
  letI : (CommRingCat.tensorProd (F.obj i) (CommRingCat.of A)).IsLeftAdjoint :=
    Functor.isLeftAdjoint_of_iso
      (CommRingCat.tensorProdIsoPushout (F.obj i) (CommRingCat.of A)).symm
  apply isColimitOfPreserves (Under.forget (CommRingCat.of A))
  apply isColimitOfPreserves (CommRingCat.tensorProd (F.obj i) (CommRingCat.of A))
  exact ringCoconeAboveIsColimit F c hc i

end BaseChangeDiagram

section StageAlgebra

variable (F : J ⥤ CommRingCat.{u})

/-- The stage ring, bundled as an algebra over `R_i`. -/
noncomputable abbrev StageRing (i : J) (X : Under i) : Under (F.obj i) :=
  (ringDiagramAbove F i).obj X

/-- The explicit algebra at a stage above `i`.  Keeping the stage ring bundled in an under
category makes its `R_i`-algebra structure available to typeclass search. -/
noncomputable abbrev StageBaseChange (i : J) (A : Type u) [CommRing A]
    [Algebra (F.obj i) A] (X : Under i) : Type u :=
  TensorProduct (F.obj i) A (StageRing F i X)

noncomputable instance stageBaseChangeAlgebra (i : J) (A : Type u) [CommRing A]
    [Algebra (F.obj i) A] (X : Under i) :
    Algebra (StageRing F i X) (StageBaseChange F i A X) :=
  Algebra.TensorProduct.rightAlgebra

/-- The copy of the fixed algebra in a finite-stage base change. -/
noncomputable def stageGenerator (i : J) (A : Type u) [CommRing A]
    [Algebra (F.obj i) A] (X : Under i) :
    A →ₐ[F.obj i] StageBaseChange F i A X :=
  Algebra.TensorProduct.includeLeft

/-- The varying base ring inside a finite-stage base change. -/
noncomputable def stageBase (i : J) (A : Type u) [CommRing A]
    [Algebra (F.obj i) A] (X : Under i) :
    StageRing F i X →ₐ[F.obj i] StageBaseChange F i A X :=
  Algebra.TensorProduct.includeRight

/-- Base change from one object above `i` to a later object. -/
noncomputable def stageTransition (i : J) (A : Type u) [CommRing A]
    [Algebra (F.obj i) A] {X Y : Under i} (f : X ⟶ Y) :
    StageBaseChange F i A X →ₐ[F.obj i] StageBaseChange F i A Y :=
  Algebra.TensorProduct.map (AlgHom.id (F.obj i) A)
    (CommRingCat.toAlgHom ((ringDiagramAbove F i).map f))

@[simp]
theorem stageTransition_stageGenerator (i : J) (A : Type u) [CommRing A]
    [Algebra (F.obj i) A] {X Y : Under i} (f : X ⟶ Y) (a : A) :
    stageTransition F i A f (stageGenerator F i A X a) = stageGenerator F i A Y a := by
  simp [stageTransition, stageGenerator]

@[simp]
theorem stageTransition_stageBase (i : J) (A : Type u) [CommRing A]
    [Algebra (F.obj i) A] {X Y : Under i} (f : X ⟶ Y) (r : StageRing F i X) :
    stageTransition F i A f (stageBase F i A X r) =
      stageBase F i A Y (CommRingCat.toAlgHom ((ringDiagramAbove F i).map f) r) := by
  simp [stageTransition, stageBase]

theorem stageTransition_comp (i : J) (A : Type u) [CommRing A]
    [Algebra (F.obj i) A] {X Y Z : Under i} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (stageTransition F i A g).comp (stageTransition F i A f) =
      stageTransition F i A (f ≫ g) := by
  ext <;> simp [stageTransition]

/-- The `R_i`-algebra structures of all terms of the varying base-change diagram. -/
noncomputable def baseChangeStructure (i : J) (A : Type u) [CommRing A]
    [Algebra (F.obj i) A] :
    (Functor.const (Under i)).obj (F.obj i) ⟶ baseChangeDiagram F i A where
  app X := CommRingCat.ofHom (algebraMap (F.obj i) (StageBaseChange F i A X))
  naturality X Y f := by
    ext r
    simp only [Functor.const_obj_obj, Functor.const_obj_map]
    change algebraMap (F.obj i) (StageBaseChange F i A Y) r =
      stageTransition F i A f (algebraMap (F.obj i) (StageBaseChange F i A X) r)
    simp [stageTransition]

@[simp]
theorem baseChangeDiagram_map_apply (i : J) (A : Type u) [CommRing A]
    [Algebra (F.obj i) A] {X Y : Under i} (f : X ⟶ Y)
    (x : StageBaseChange F i A X) :
    (baseChangeDiagram F i A).map f x = stageTransition F i A f x :=
  rfl

section Limit

variable (c : Cocone F)

/-- The colimit ring, bundled as an algebra over the selected stage. -/
noncomputable abbrev LimitRing (i : J) : Under (F.obj i) := Under.mk (c.ι.app i)

/-- Base change of a fixed stage algebra to the colimit ring. -/
noncomputable abbrev LimitBaseChange (i : J) (A : Type u) [CommRing A]
    [Algebra (F.obj i) A] : Type u :=
  TensorProduct (F.obj i) A (LimitRing F c i)

noncomputable instance limitBaseChangeAlgebra (i : J) (A : Type u) [CommRing A]
    [Algebra (F.obj i) A] :
    Algebra (LimitRing F c i) (LimitBaseChange F c i A) :=
  Algebra.TensorProduct.rightAlgebra

/-- The fixed generators in the colimit base change. -/
noncomputable def limitGenerator (i : J) (A : Type u) [CommRing A]
    [Algebra (F.obj i) A] : A →ₐ[F.obj i] LimitBaseChange F c i A :=
  Algebra.TensorProduct.includeLeft

/-- The colimit ring in the colimit base change. -/
noncomputable def limitBase (i : J) (A : Type u) [CommRing A]
    [Algebra (F.obj i) A] :
    LimitRing F c i →ₐ[F.obj i] LimitBaseChange F c i A :=
  Algebra.TensorProduct.includeRight

/-- The canonical map from a finite-stage base change to the colimit base change. -/
noncomputable def stageToLimit (i : J) (A : Type u) [CommRing A]
    [Algebra (F.obj i) A] (X : Under i) :
    StageBaseChange F i A X →ₐ[F.obj i] LimitBaseChange F c i A :=
  Algebra.TensorProduct.map (AlgHom.id (F.obj i) A)
    (CommRingCat.toAlgHom ((ringCoconeAbove F c i).ι.app X))

@[simp]
theorem stageToLimit_stageGenerator (i : J) (A : Type u) [CommRing A]
    [Algebra (F.obj i) A] (X : Under i) (a : A) :
    stageToLimit F c i A X (stageGenerator F i A X a) = limitGenerator F c i A a := by
  simp only [stageToLimit, stageGenerator, limitGenerator, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  congr 1
  exact (CommRingCat.toAlgHom ((ringCoconeAbove F c i).ι.app X)).map_one

@[simp]
theorem stageToLimit_stageBase (i : J) (A : Type u) [CommRing A]
    [Algebra (F.obj i) A] (X : Under i) (r : StageRing F i X) :
    stageToLimit F c i A X (stageBase F i A X r) =
      limitBase F c i A (CommRingCat.toAlgHom ((ringCoconeAbove F c i).ι.app X) r) := by
  rfl

@[simp]
theorem baseChangeCocone_ι_apply (i : J) (A : Type u) [CommRing A]
    [Algebra (F.obj i) A] (X : Under i) (x : StageBaseChange F i A X) :
    (baseChangeCocone F c i A).ι.app X x = stageToLimit F c i A X x :=
  rfl

/-- The map to the colimit is compatible with every finite-stage transition. -/
theorem stageToLimit_stageTransition (i : J) (A : Type u) [CommRing A]
    [Algebra (F.obj i) A] {X Y : Under i} (f : X ⟶ Y)
    (x : StageBaseChange F i A X) :
    stageToLimit F c i A Y (stageTransition F i A f x) = stageToLimit F c i A X x := by
  change (baseChangeCocone F c i A).ι.app Y
      ((baseChangeDiagram F i A).map f x) = (baseChangeCocone F c i A).ι.app X x
  have h := congrArg (fun k ↦ k x) ((baseChangeCocone F c i A).w f)
  change (baseChangeCocone F c i A).ι.app Y
      ((baseChangeDiagram F i A).map f x) = (baseChangeCocone F c i A).ι.app X x at h
  exact h

end Limit

/-- A map on the fixed generators extends uniquely to a homomorphism of algebras over the
varying stage ring. -/
noncomputable def extendAtStage (i : J) (A B : Type u) [CommRing A] [CommRing B]
    [Algebra (F.obj i) A] [Algebra (F.obj i) B] (X : Under i)
    (g : A →ₐ[F.obj i] StageBaseChange F i B X) :
    StageBaseChange F i A X →ₐ[StageRing F i X] StageBaseChange F i B X := by
  let h : StageBaseChange F i A X →ₐ[F.obj i] StageBaseChange F i B X :=
    Algebra.TensorProduct.productMap g (stageBase F i B X)
  exact
    { __ := h.toRingHom
      commutes' := fun r ↦ by
        change h (1 ⊗ₜ r) = 1 ⊗ₜ r
        simp [h, stageBase] }

@[simp]
theorem extendAtStage_stageGenerator (i : J) (A B : Type u) [CommRing A] [CommRing B]
    [Algebra (F.obj i) A] [Algebra (F.obj i) B] (X : Under i)
    (g : A →ₐ[F.obj i] StageBaseChange F i B X) (a : A) :
    extendAtStage F i A B X g (stageGenerator F i A X a) = g a := by
  simp [extendAtStage, stageGenerator]

@[simp]
theorem extendAtStage_stageBase (i : J) (A B : Type u) [CommRing A] [CommRing B]
    [Algebra (F.obj i) A] [Algebra (F.obj i) B] (X : Under i)
    (g : A →ₐ[F.obj i] StageBaseChange F i B X) (r : StageRing F i X) :
    extendAtStage F i A B X g (stageBase F i A X r) = stageBase F i B X r := by
  simp [extendAtStage, stageBase]

/-- Extending a map from the fixed generators commutes with passage to a later stage. -/
theorem stageTransition_extendAtStage (i : J) (A B : Type u) [CommRing A] [CommRing B]
    [Algebra (F.obj i) A] [Algebra (F.obj i) B] {X Y : Under i} (f : X ⟶ Y)
    (g : A →ₐ[F.obj i] StageBaseChange F i B X) (x : StageBaseChange F i A X) :
    stageTransition F i B f (extendAtStage F i A B X g x) =
      extendAtStage F i A B Y ((stageTransition F i B f).comp g)
        (stageTransition F i A f x) := by
  let lhs : StageBaseChange F i A X →ₐ[F.obj i] StageBaseChange F i B Y :=
    (stageTransition F i B f).comp ((extendAtStage F i A B X g).restrictScalars (F.obj i))
  let rhs : StageBaseChange F i A X →ₐ[F.obj i] StageBaseChange F i B Y :=
    ((extendAtStage F i A B Y ((stageTransition F i B f).comp g)).restrictScalars
      (F.obj i)).comp (stageTransition F i A f)
  have h : lhs = rhs := by
    apply Algebra.TensorProduct.ext
    · apply AlgHom.ext
      intro a
      change stageTransition F i B f
          (extendAtStage F i A B X g (stageGenerator F i A X a)) =
        extendAtStage F i A B Y ((stageTransition F i B f).comp g)
          (stageTransition F i A f (stageGenerator F i A X a))
      rw [extendAtStage_stageGenerator, stageTransition_stageGenerator,
        extendAtStage_stageGenerator]
      rfl
    · apply AlgHom.ext
      intro r
      change stageTransition F i B f
          (extendAtStage F i A B X g (stageBase F i A X r)) =
        extendAtStage F i A B Y ((stageTransition F i B f).comp g)
          (stageTransition F i A f (stageBase F i A X r))
      rw [extendAtStage_stageBase, stageTransition_stageBase,
        stageTransition_stageBase, extendAtStage_stageBase]
  exact AlgHom.congr_fun h x

/-- A homomorphism out of a finite-stage base change, linear over the varying stage ring, is
determined by the fixed generators. -/
theorem stageAlgHom_ext (i : J) (A C : Type u) [CommRing A] [CommRing C]
    [Algebra (F.obj i) A] (X : Under i) [Algebra (StageRing F i X) C]
    (f g : StageBaseChange F i A X →ₐ[StageRing F i X] C)
    (h : ∀ a, f (stageGenerator F i A X a) = g (stageGenerator F i A X a)) : f = g := by
  apply AlgHom.ext
  intro x
  refine x.inductionOn ?_ ?_
  · intro a r
    have ht : a ⊗ₜ[F.obj i] r =
        stageGenerator F i A X a * algebraMap (StageRing F i X) (StageBaseChange F i A X) r := by
      change a ⊗ₜ[F.obj i] r = (a ⊗ₜ[F.obj i] 1) * (1 ⊗ₜ[F.obj i] r)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [ht, map_mul, map_mul, h, f.commutes, g.commutes]
  · intro x y hx hy
    simp [hx, hy]

section EquivalenceDescent

variable (c : Cocone F) (hc : IsColimit c)

/-- The forward map on the fixed generators induced by an isomorphism after passage to the
filtered colimit. -/
noncomputable def limitForwardGenerators (i : J) (A B : Type u) [CommRing A] [CommRing B]
    [Algebra (F.obj i) A] [Algebra (F.obj i) B]
    (e : LimitBaseChange F c i A ≃ₐ[LimitRing F c i] LimitBaseChange F c i B) :
    A →ₐ[F.obj i] LimitBaseChange F c i B :=
  (e.toAlgHom.restrictScalars (F.obj i)).comp (limitGenerator F c i A)

/-- The inverse map on the fixed generators induced by an isomorphism after passage to the
filtered colimit. -/
noncomputable def limitInverseGenerators (i : J) (A B : Type u) [CommRing A] [CommRing B]
    [Algebra (F.obj i) A] [Algebra (F.obj i) B]
    (e : LimitBaseChange F c i A ≃ₐ[LimitRing F c i] LimitBaseChange F c i B) :
    B →ₐ[F.obj i] LimitBaseChange F c i A :=
  (e.symm.toAlgHom.restrictScalars (F.obj i)).comp (limitGenerator F c i B)

/-- Two finite-stage maps whose passage to the colimit agrees with an isomorphism and its
inverse on the fixed generators. -/
structure DescendedMapPair (i : J) (A B : Type u) [CommRing A] [CommRing B]
    [Algebra (F.obj i) A] [Algebra (F.obj i) B]
    (e : LimitBaseChange F c i A ≃ₐ[LimitRing F c i] LimitBaseChange F c i B) where
  stage : Under i
  forward : A →ₐ[F.obj i] StageBaseChange F i B stage
  inverse : B →ₐ[F.obj i] StageBaseChange F i A stage
  forward_toLimit : (stageToLimit F c i B stage).comp forward = limitForwardGenerators F c i A B e
  inverse_toLimit : (stageToLimit F c i A stage).comp inverse = limitInverseGenerators F c i A B e

/-- A finite-stage algebra equivalence whose two generator maps recover the prescribed
equivalence and its inverse after passage to the filtered colimit. -/
structure DescendedAlgEquiv (i : J) (A B : Type u) [CommRing A] [CommRing B]
    [Algebra (F.obj i) A] [Algebra (F.obj i) B]
    (e : LimitBaseChange F c i A ≃ₐ[LimitRing F c i] LimitBaseChange F c i B) where
  stage : Under i
  equiv : StageBaseChange F i A stage ≃ₐ[StageRing F i stage] StageBaseChange F i B stage
  forward_toLimit :
    (stageToLimit F c i B stage).comp
        ((equiv.toAlgHom.restrictScalars (F.obj i)).comp (stageGenerator F i A stage)) =
      limitForwardGenerators F c i A B e
  inverse_toLimit :
    (stageToLimit F c i A stage).comp
        ((equiv.symm.toAlgHom.restrictScalars (F.obj i)).comp (stageGenerator F i B stage)) =
      limitInverseGenerators F c i A B e

include hc
/-- The map-existence clause of Tag `05N9`, applied simultaneously to an isomorphism and its
inverse after constructing the two varying base-change diagrams. -/
theorem exists_descendedMapPair (i : J) (A B : Type u) [CommRing A] [CommRing B]
    [Algebra (F.obj i) A] [Algebra (F.obj i) B]
    [IsFiltered J]
    (hA : Algebra.FinitePresentation (F.obj i) A)
    (hB : Algebra.FinitePresentation (F.obj i) B)
    (e : LimitBaseChange F c i A ≃ₐ[LimitRing F c i] LimitBaseChange F c i B) :
    Nonempty (DescendedMapPair F c i A B e) := by
  let fA : CommRingCat.of (F.obj i) ⟶ CommRingCat.of A :=
    CommRingCat.ofHom (algebraMap (F.obj i) A)
  let fB : CommRingCat.of (F.obj i) ⟶ CommRingCat.of B :=
    CommRingCat.ofHom (algebraMap (F.obj i) B)
  let a : CommRingCat.of A ⟶ (baseChangeCocone F c i B).pt :=
    CommRingCat.ofHom (limitForwardGenerators F c i A B e).toRingHom
  let b : CommRingCat.of B ⟶ (baseChangeCocone F c i A).pt :=
    CommRingCat.ofHom (limitInverseGenerators F c i A B e).toRingHom
  have ha : ∀ X, fA ≫ a = (baseChangeStructure F i B).app X ≫
      (baseChangeCocone F c i B).ι.app X := by
    intro X
    ext r
    change limitForwardGenerators F c i A B e (algebraMap (F.obj i) A r) = _
    rw [AlgHom.commutes]
    rw [← AlgHom.commutes (stageToLimit F c i B X) r]
    exact congrArg (stageToLimit F c i B X)
      (AlgHom.commutes (stageGenerator F i B X) r).symm
  have hb : ∀ X, fB ≫ b = (baseChangeStructure F i A).app X ≫
      (baseChangeCocone F c i A).ι.app X := by
    intro X
    ext r
    change limitInverseGenerators F c i A B e (algebraMap (F.obj i) B r) = _
    rw [AlgHom.commutes]
    rw [← AlgHom.commutes (stageToLimit F c i A X) r]
    exact congrArg (stageToLimit F c i A X)
      (AlgHom.commutes (stageGenerator F i A X) r).symm
  obtain ⟨X, aX, bX, hfaX, haX, hfbX, hbX⟩ :=
    exists_common_factorizations_of_finitePresentation
      (baseChangeDiagram F i B) (baseChangeCocone F c i B)
      (baseChangeCoconeIsColimit F c hc i B)
      (CommRingCat.of (F.obj i)) (baseChangeDiagram F i A)
      (baseChangeStructure F i B) (baseChangeStructure F i A)
      (baseChangeCocone F c i A)
      (baseChangeCoconeIsColimit F c hc i A)
      fA fB
      (RingHom.finitePresentation_algebraMap.mpr hA)
      (RingHom.finitePresentation_algebraMap.mpr hB) a b ha hb
  let aX' : A →ₐ[F.obj i] StageBaseChange F i B X :=
    { __ := aX.hom
      commutes' := fun r ↦ by
        have hr := congr($(hfaX).hom r)
        change aX.hom (algebraMap (F.obj i) A r) =
          algebraMap (F.obj i) (StageBaseChange F i B X) r at hr
        exact hr }
  let bX' : B →ₐ[F.obj i] StageBaseChange F i A X :=
    { __ := bX.hom
      commutes' := fun r ↦ by
        have hr := congr($(hfbX).hom r)
        change bX.hom (algebraMap (F.obj i) B r) =
          algebraMap (F.obj i) (StageBaseChange F i A X) r at hr
        exact hr }
  refine ⟨⟨X, aX', bX', ?_, ?_⟩⟩
  · ext x
    exact congr($(haX).hom x).symm
  · ext x
    exact congr($(hbX).hom x).symm

omit hc

/-- The composite "inverse after forward" of a descended map pair agrees with the identity
after passage to the colimit. -/
theorem DescendedMapPair.inverse_comp_forward_toLimit
    {i : J} {A B : Type u} [CommRing A] [CommRing B]
    [Algebra (F.obj i) A] [Algebra (F.obj i) B]
    {e : LimitBaseChange F c i A ≃ₐ[LimitRing F c i] LimitBaseChange F c i B}
    (P : DescendedMapPair F c i A B e) :
    (stageToLimit F c i A P.stage).comp
        (((extendAtStage F i B A P.stage P.inverse).restrictScalars (F.obj i)).comp
          P.forward) =
      (stageToLimit F c i A P.stage).comp (stageGenerator F i A P.stage) := by
  have hInverse :
      (stageToLimit F c i A P.stage).comp
          ((extendAtStage F i B A P.stage P.inverse).restrictScalars (F.obj i)) =
        (e.symm.toAlgHom.restrictScalars (F.obj i)).comp
          (stageToLimit F c i B P.stage) := by
    apply Algebra.TensorProduct.ext
    · apply AlgHom.ext
      intro b
      change stageToLimit F c i A P.stage
          (extendAtStage F i B A P.stage P.inverse (stageGenerator F i B P.stage b)) =
        e.symm (stageToLimit F c i B P.stage (stageGenerator F i B P.stage b))
      rw [extendAtStage_stageGenerator, stageToLimit_stageGenerator]
      simpa [limitInverseGenerators] using AlgHom.congr_fun P.inverse_toLimit b
    · apply AlgHom.ext
      intro r
      change stageToLimit F c i A P.stage
          (extendAtStage F i B A P.stage P.inverse (stageBase F i B P.stage r)) =
        e.symm (stageToLimit F c i B P.stage (stageBase F i B P.stage r))
      rw [extendAtStage_stageBase, stageToLimit_stageBase, stageToLimit_stageBase]
      exact (e.symm.commutes _).symm
  apply AlgHom.ext
  intro a
  change stageToLimit F c i A P.stage
      (extendAtStage F i B A P.stage P.inverse (P.forward a)) =
    stageToLimit F c i A P.stage (stageGenerator F i A P.stage a)
  have hInv := AlgHom.congr_fun hInverse (P.forward a)
  change stageToLimit F c i A P.stage
      (extendAtStage F i B A P.stage P.inverse (P.forward a)) =
    e.symm (stageToLimit F c i B P.stage (P.forward a)) at hInv
  rw [hInv]
  have hFor := AlgHom.congr_fun P.forward_toLimit a
  change stageToLimit F c i B P.stage (P.forward a) =
    limitForwardGenerators F c i A B e a at hFor
  rw [hFor]
  simp [limitForwardGenerators]

/-- The composite "forward after inverse" of a descended map pair agrees with the identity
after passage to the colimit. -/
theorem DescendedMapPair.forward_comp_inverse_toLimit
    {i : J} {A B : Type u} [CommRing A] [CommRing B]
    [Algebra (F.obj i) A] [Algebra (F.obj i) B]
    {e : LimitBaseChange F c i A ≃ₐ[LimitRing F c i] LimitBaseChange F c i B}
    (P : DescendedMapPair F c i A B e) :
    (stageToLimit F c i B P.stage).comp
        (((extendAtStage F i A B P.stage P.forward).restrictScalars (F.obj i)).comp
          P.inverse) =
      (stageToLimit F c i B P.stage).comp (stageGenerator F i B P.stage) := by
  have hForward :
      (stageToLimit F c i B P.stage).comp
          ((extendAtStage F i A B P.stage P.forward).restrictScalars (F.obj i)) =
        (e.toAlgHom.restrictScalars (F.obj i)).comp
          (stageToLimit F c i A P.stage) := by
    apply Algebra.TensorProduct.ext
    · apply AlgHom.ext
      intro a
      change stageToLimit F c i B P.stage
          (extendAtStage F i A B P.stage P.forward (stageGenerator F i A P.stage a)) =
        e (stageToLimit F c i A P.stage (stageGenerator F i A P.stage a))
      rw [extendAtStage_stageGenerator, stageToLimit_stageGenerator]
      simpa [limitForwardGenerators] using AlgHom.congr_fun P.forward_toLimit a
    · apply AlgHom.ext
      intro r
      change stageToLimit F c i B P.stage
          (extendAtStage F i A B P.stage P.forward (stageBase F i A P.stage r)) =
        e (stageToLimit F c i A P.stage (stageBase F i A P.stage r))
      rw [extendAtStage_stageBase, stageToLimit_stageBase, stageToLimit_stageBase]
      exact (e.commutes _).symm
  apply AlgHom.ext
  intro b
  change stageToLimit F c i B P.stage
      (extendAtStage F i A B P.stage P.forward (P.inverse b)) =
    stageToLimit F c i B P.stage (stageGenerator F i B P.stage b)
  have hFor := AlgHom.congr_fun hForward (P.inverse b)
  change stageToLimit F c i B P.stage
      (extendAtStage F i A B P.stage P.forward (P.inverse b)) =
    e (stageToLimit F c i A P.stage (P.inverse b)) at hFor
  rw [hFor]
  have hInv := AlgHom.congr_fun P.inverse_toLimit b
  change stageToLimit F c i A P.stage (P.inverse b) =
    limitInverseGenerators F c i A B e b at hInv
  rw [hInv]
  simp [limitInverseGenerators]

include hc
/-- Exact coherent isomorphism descent from Tag `05N9`: a finitely presented algebra
equivalence over a filtered colimit is induced at one finite stage, with both directions
compatible with the original equivalence on the fixed generators. -/
theorem exists_descendedAlgEquiv (i : J) (A B : Type u) [CommRing A] [CommRing B]
    [Algebra (F.obj i) A] [Algebra (F.obj i) B]
    [IsFiltered J]
    (hA : Algebra.FinitePresentation (F.obj i) A)
    (hB : Algebra.FinitePresentation (F.obj i) B)
    (e : LimitBaseChange F c i A ≃ₐ[LimitRing F c i] LimitBaseChange F c i B) :
    Nonempty (DescendedAlgEquiv F c i A B e) := by
  obtain ⟨P⟩ := exists_descendedMapPair F c hc i A B hA hB e
  let fA : CommRingCat.of (F.obj i) ⟶ CommRingCat.of A :=
    CommRingCat.ofHom (algebraMap (F.obj i) A)
  let fB : CommRingCat.of (F.obj i) ⟶ CommRingCat.of B :=
    CommRingCat.ofHom (algebraMap (F.obj i) B)
  let compA : CommRingCat.of A ⟶ (baseChangeDiagram F i A).obj P.stage :=
    CommRingCat.ofHom
      (((extendAtStage F i B A P.stage P.inverse).restrictScalars (F.obj i)).comp
        P.forward).toRingHom
  let idA : CommRingCat.of A ⟶ (baseChangeDiagram F i A).obj P.stage :=
    CommRingCat.ofHom (stageGenerator F i A P.stage).toRingHom
  let compB : CommRingCat.of B ⟶ (baseChangeDiagram F i B).obj P.stage :=
    CommRingCat.ofHom
      (((extendAtStage F i A B P.stage P.forward).restrictScalars (F.obj i)).comp
        P.inverse).toRingHom
  let idB : CommRingCat.of B ⟶ (baseChangeDiagram F i B).obj P.stage :=
    CommRingCat.ofHom (stageGenerator F i B P.stage).toRingHom
  have hCompA : fA ≫ compA = (baseChangeStructure F i A).app P.stage := by
    ext r
    change (((extendAtStage F i B A P.stage P.inverse).restrictScalars (F.obj i)).comp
      P.forward) (algebraMap (F.obj i) A r) =
        algebraMap (F.obj i) (StageBaseChange F i A P.stage) r
    exact AlgHom.commutes _ r
  have hIdA : fA ≫ idA = (baseChangeStructure F i A).app P.stage := by
    ext r
    change stageGenerator F i A P.stage (algebraMap (F.obj i) A r) =
      algebraMap (F.obj i) (StageBaseChange F i A P.stage) r
    exact AlgHom.commutes _ r
  have hCompB : fB ≫ compB = (baseChangeStructure F i B).app P.stage := by
    ext r
    change (((extendAtStage F i A B P.stage P.forward).restrictScalars (F.obj i)).comp
      P.inverse) (algebraMap (F.obj i) B r) =
        algebraMap (F.obj i) (StageBaseChange F i B P.stage) r
    exact AlgHom.commutes _ r
  have hIdB : fB ≫ idB = (baseChangeStructure F i B).app P.stage := by
    ext r
    change stageGenerator F i B P.stage (algebraMap (F.obj i) B r) =
      algebraMap (F.obj i) (StageBaseChange F i B P.stage) r
    exact AlgHom.commutes _ r
  have hColimA :
      compA ≫ (baseChangeCocone F c i A).ι.app P.stage =
        idA ≫ (baseChangeCocone F c i A).ι.app P.stage := by
    ext a
    exact AlgHom.congr_fun (P.inverse_comp_forward_toLimit (F := F) (c := c)) a
  have hColimB :
      compB ≫ (baseChangeCocone F c i B).ι.app P.stage =
        idB ≫ (baseChangeCocone F c i B).ι.app P.stage := by
    ext b
    exact AlgHom.congr_fun (P.forward_comp_inverse_toLimit (F := F) (c := c)) b
  obtain ⟨M, hAc, hAi, hBc, hBi, hEqA, hEqB⟩ :=
    exists_common_stage_for_two_eventual_eq_of_finitePresentation
      (baseChangeDiagram F i A) (baseChangeCocone F c i A)
      (baseChangeCoconeIsColimit F c hc i A)
      (CommRingCat.of (F.obj i)) (baseChangeDiagram F i B)
      (baseChangeStructure F i A) (baseChangeStructure F i B)
      (baseChangeCocone F c i B) (baseChangeCoconeIsColimit F c hc i B)
      fA fB
      (RingHom.finitePresentation_algebraMap.mpr hA)
      (RingHom.finitePresentation_algebraMap.mpr hB)
      compA hCompA idA hIdA compB hCompB idB hIdB hColimA hColimB
  let N : Under i := IsFiltered.coeq hAc hBc
  let q : M ⟶ N := IsFiltered.coeqHom hAc hBc
  let p : P.stage ⟶ N := hAc ≫ q
  have hpB : p = hBc ≫ q := IsFiltered.coeq_condition hAc hBc
  let forwardN : A →ₐ[F.obj i] StageBaseChange F i B N :=
    (stageTransition F i B p).comp P.forward
  let inverseN : B →ₐ[F.obj i] StageBaseChange F i A N :=
    (stageTransition F i A p).comp P.inverse
  let forwardAlg : StageBaseChange F i A N →ₐ[StageRing F i N] StageBaseChange F i B N :=
    extendAtStage F i A B N forwardN
  let inverseAlg : StageBaseChange F i B N →ₐ[StageRing F i N] StageBaseChange F i A N :=
    extendAtStage F i B A N inverseN
  have hEqA_apply (a : A) :
      stageTransition F i A hAc
          (extendAtStage F i B A P.stage P.inverse (P.forward a)) =
        stageTransition F i A hAi (stageGenerator F i A P.stage a) := by
    have h := congrArg (fun k ↦ k a) hEqA
    exact h
  have hEqB_apply (b : B) :
      stageTransition F i B hBc
          (extendAtStage F i A B P.stage P.forward (P.inverse b)) =
        stageTransition F i B hBi (stageGenerator F i B P.stage b) := by
    have h := congrArg (fun k ↦ k b) hEqB
    exact h
  have hLeftGenerators (a : A) :
      inverseAlg (forwardAlg (stageGenerator F i A N a)) = stageGenerator F i A N a := by
    change extendAtStage F i B A N inverseN
        (extendAtStage F i A B N forwardN (stageGenerator F i A N a)) = _
    rw [extendAtStage_stageGenerator]
    change extendAtStage F i B A N inverseN (stageTransition F i B p (P.forward a)) = _
    rw [← stageTransition_extendAtStage]
    calc
      stageTransition F i A p
          (extendAtStage F i B A P.stage P.inverse (P.forward a)) =
          stageTransition F i A q
            (stageTransition F i A hAc
              (extendAtStage F i B A P.stage P.inverse (P.forward a))) :=
        (AlgHom.congr_fun (stageTransition_comp F i A hAc q) _).symm
      _ = stageTransition F i A q
          (stageTransition F i A hAi (stageGenerator F i A P.stage a)) := by
        rw [hEqA_apply]
      _ = stageGenerator F i A N a := by simp
  have hRightGenerators (b : B) :
      forwardAlg (inverseAlg (stageGenerator F i B N b)) = stageGenerator F i B N b := by
    change extendAtStage F i A B N forwardN
        (extendAtStage F i B A N inverseN (stageGenerator F i B N b)) = _
    rw [extendAtStage_stageGenerator]
    change extendAtStage F i A B N forwardN (stageTransition F i A p (P.inverse b)) = _
    rw [← stageTransition_extendAtStage]
    calc
      stageTransition F i B p
          (extendAtStage F i A B P.stage P.forward (P.inverse b)) =
          stageTransition F i B q
            (stageTransition F i B hBc
              (extendAtStage F i A B P.stage P.forward (P.inverse b))) := by
        rw [hpB]
        exact (AlgHom.congr_fun (stageTransition_comp F i B hBc q) _).symm
      _ = stageTransition F i B q
          (stageTransition F i B hBi (stageGenerator F i B P.stage b)) := by
        rw [hEqB_apply]
      _ = stageGenerator F i B N b := by simp
  have hLeft : inverseAlg.comp forwardAlg = AlgHom.id (StageRing F i N) _ := by
    apply stageAlgHom_ext F i A _ N
    intro a
    exact hLeftGenerators a
  have hRight : forwardAlg.comp inverseAlg = AlgHom.id (StageRing F i N) _ := by
    apply stageAlgHom_ext F i B _ N
    intro b
    exact hRightGenerators b
  let equivN : StageBaseChange F i A N ≃ₐ[StageRing F i N] StageBaseChange F i B N :=
    AlgEquiv.ofAlgHom forwardAlg inverseAlg hRight hLeft
  refine ⟨⟨N, equivN, ?_, ?_⟩⟩
  · apply AlgHom.ext
    intro a
    change stageToLimit F c i B N
        (forwardAlg (stageGenerator F i A N a)) = limitForwardGenerators F c i A B e a
    rw [show forwardAlg (stageGenerator F i A N a) = forwardN a by
      exact extendAtStage_stageGenerator F i A B N forwardN a]
    change stageToLimit F c i B N (stageTransition F i B p (P.forward a)) = _
    rw [stageToLimit_stageTransition]
    have h := AlgHom.congr_fun P.forward_toLimit a
    exact h
  · apply AlgHom.ext
    intro b
    change stageToLimit F c i A N
        (inverseAlg (stageGenerator F i B N b)) = limitInverseGenerators F c i A B e b
    rw [show inverseAlg (stageGenerator F i B N b) = inverseN b by
      exact extendAtStage_stageGenerator F i B A N inverseN b]
    change stageToLimit F c i A N (stageTransition F i A p (P.inverse b)) = _
    rw [stageToLimit_stageTransition]
    have h := AlgHom.congr_fun P.inverse_toLimit b
    exact h

/-- The `05N9` isomorphism descent package when the left algebra is the finite disjoint
union of standard tame covers from Tags `0EYG` and `0EYH`. -/
theorem exists_descendedAlgEquiv_of_standardTameCover
    (i : J) (A B : Type u) [CommRing A] [CommRing B]
    [Algebra (F.obj i) A] [Algebra (F.obj i) B] [IsNoetherianRing (F.obj i)]
    [IsFiltered J]
    {a : F.obj i} (hA : IsFiniteDisjointUnionOfStandardTameCovers (F.obj i) A a)
    (hB : Algebra.FinitePresentation (F.obj i) B)
    (e : LimitBaseChange F c i A ≃ₐ[LimitRing F c i] LimitBaseChange F c i B) :
    Nonempty (DescendedAlgEquiv F c i A B e) :=
  exists_descendedAlgEquiv F c hc i A B hA.finitePresentation hB e

/-- Symmetric standard-cover specialization: two finite disjoint unions of standard tame
covers that become equivalent over the colimit are already equivalent after one finite
stage. -/
theorem exists_descendedAlgEquiv_of_standardTameCovers
    (i : J) (A B : Type u) [CommRing A] [CommRing B]
    [Algebra (F.obj i) A] [Algebra (F.obj i) B] [IsNoetherianRing (F.obj i)]
    [IsFiltered J]
    {a b : F.obj i}
    (hA : IsFiniteDisjointUnionOfStandardTameCovers (F.obj i) A a)
    (hB : IsFiniteDisjointUnionOfStandardTameCovers (F.obj i) B b)
    (e : LimitBaseChange F c i A ≃ₐ[LimitRing F c i] LimitBaseChange F c i B) :
    Nonempty (DescendedAlgEquiv F c i A B e) :=
  exists_descendedAlgEquiv F c hc i A B hA.finitePresentation hB.finitePresentation e

end EquivalenceDescent

end StageAlgebra

#print axioms ringCoconeAboveIsColimit
#print axioms baseChangeCoconeIsColimit
#print axioms exists_descendedMapPair
#print axioms exists_descendedAlgEquiv
#print axioms exists_descendedAlgEquiv_of_standardTameCover
#print axioms exists_descendedAlgEquiv_of_standardTameCovers

end Pcf.Stacks.EtaleDescent
