/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Palomar.Statement
public import Pcf.Bounding.PcfAllTheWayDownCharZero

/-!
# Bridge from the Palomar statement surface to the development

The compact notions of `Pcf.Palomar.Statement` agree with the development's:

* `isPCF_iff_divisorDynamics_isPCF`: `IsPCF` of a finite dominant endomorphism of a normal
  Noetherian
  integral scheme is `DivisorDynamics.IsPCF` of its divisor dynamics;
* `isNormalizationLift_unique` / `isNormalizationLift_lift`: the canonical normalization lift
  `schemeGlobalNormalizationLift f` is the unique `IsNormalizationLift`, so
  `IsNormalizedPCF f ↔ IsNormalizedPCFOfFiniteType k s f`;
* `iterateHom_eq_pow`, `iterateHom_apply`: iterates agree with `End` powers;
* `pcfAllTheWayDownAtDepth_of_scheme`: the development's recursive predicate implies the
  compact one.

The compared theorem `Pcf.Palomar.pcfAllTheWayDown_charZero_unconditional`
(`Pcf.Palomar.Unconditional`) is derived through these equivalences from
`Pcf.pcfAllTheWayDown_charZero_unconditional`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf.Palomar

noncomputable section

set_option linter.style.haveILetI false

/-! ## Iterates -/

theorem iterateHom_eq_pow {X : Scheme.{u}} (f : X ⟶ X) (n : ℕ) :
    iterateHom f n = (End.of f ^ n).asHom := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterateHom, ih, pow_succ', End.mul_asHom]

theorem iterateHom_apply {X : Scheme.{u}} (f : X ⟶ X) (n : ℕ) (x : X) :
    iterateHom f n x = (⇑f)^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterateHom, Scheme.Hom.comp_apply, ih, Function.iterate_succ_apply']

theorem endPow_apply {X : Scheme.{u}} (f : X ⟶ X) (n : ℕ) (x : X) :
    (End.of f ^ n).asHom x = (⇑f)^[n] x := by
  rw [← iterateHom_eq_pow, iterateHom_apply]

/-! ## Post-critical finiteness -/

theorem divisorDynamics_step_iterate_val {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X] [NoetherianSpace X]
    [CharZero (X.presheaf.stalk (genericPoint X))] (n : ℕ) (x : SchemeDivisorPoint X) :
    ((divisorDynamicsOfFiniteDominantNormalCharZero f).step^[n] x).1 = (⇑f)^[n] x.1 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply]
      rfl

/-- `IsPCF` is the post-critical finiteness of the development's divisor dynamics. -/
theorem isPCF_iff_divisorDynamics_isPCF {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X] [NoetherianSpace X]
    [CharZero (X.presheaf.stalk (genericPoint X))] :
    IsPCF f ↔ (divisorDynamicsOfFiniteDominantNormalCharZero f).IsPCF := by
  let D := divisorDynamicsOfFiniteDominantNormalCharZero f
  have himage : Subtype.val '' D.postcriticalSet = postcriticalSet f := by
    ext y
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      obtain ⟨n, R, ⟨Q', hQ'R, hram⟩, hRQ⟩ := D.mem_postcriticalSet_iff.mp hQ
      refine ⟨Q'.1, Q'.2, hram, n, ?_⟩
      rw [← hRQ, ← hQ'R, ← Function.iterate_succ_apply, divisorDynamics_step_iterate_val]
    · rintro ⟨x, hx, hram, n, rfl⟩
      let Q' : SchemeDivisorPoint X := ⟨x, hx⟩
      refine ⟨D.step^[n] (D.step Q'), D.mem_postcriticalSet_iff.mpr
          ⟨n, D.step Q', ⟨Q', rfl, hram⟩, rfl⟩,
        ?_⟩
      rw [← Function.iterate_succ_apply, divisorDynamics_step_iterate_val]
  unfold IsPCF DivisorDynamics.IsPCF
  rw [← himage]
  exact Set.finite_image_iff Subtype.val_injective.injOn

/-! ## Normalization lifts -/

/-- There is at most one lift of `f` to the normalization. -/
theorem isNormalizationLift_unique {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ X)
    {g₁ g₂ : normalization X ⟶ normalization X}
    (h₁ : IsNormalizationLift f g₁) (h₂ : IsNormalizationLift f g₂) : g₁ = g₂ := by
  obtain ⟨hn₁, v₁, hv₁⟩ := h₁
  obtain ⟨hn₂, v₂, hv₂⟩ := h₂
  have hv (g : normalization X ⟶ normalization X) (v)
      (hn : g ≫ normalizationMap X = normalizationMap X ≫ f)
      (hv : genericToNormalization X ≫ g = v ≫ genericToNormalization X) :
      v ≫ X.fromSpecStalk (genericPoint X) = X.fromSpecStalk (genericPoint X) ≫ f := by
    have hc : genericToNormalization X ≫ normalizationMap X = X.fromSpecStalk (genericPoint X) :=
      schemeGenericToNormalization_comp X
    rw [← hc, ← Category.assoc, ← hv, Category.assoc, hn, ← Category.assoc, hc]
  have hvv : v₁ = v₂ := (cancel_mono (X.fromSpecStalk (genericPoint X))).mp
    ((hv g₁ v₁ hn₁ hv₁).trans (hv g₂ v₂ hn₂ hv₂).symm)
  subst hvv
  exact ext_of_isDominant_of_isSeparated (normalizationMap X) (hn₁.trans hn₂.symm)
    (genericToNormalization X) (hv₁.trans hv₂.symm)

/-- The canonical lift of the development is a lift. -/
theorem isNormalizationLift_lift {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ X)
    [IsFinite f] [IsDominant f] :
    IsNormalizationLift f (schemeGlobalNormalizationLift f) :=
  ⟨schemeGlobalNormalizationLift_comp f, schemeGenericMorphism f,
    schemeGenericToNormalization_morphism f⟩

/-- Lifts to the normalization exist and are unique. -/
theorem existsUnique_isNormalizationLift {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ X)
    [IsFinite f] [IsDominant f] :
    ∃! g : normalization X ⟶ normalization X, IsNormalizationLift f g :=
  ⟨_, isNormalizationLift_lift f, fun _ hg ↦ isNormalizationLift_unique f hg
    (isNormalizationLift_lift f)⟩

theorem isNormalizedPCF_iff_lift {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ X)
    [IsFinite f] [IsDominant f] :
    IsNormalizedPCF f ↔ IsPCF (schemeGlobalNormalizationLift f) := by
  refine ⟨fun h ↦ h _ (isNormalizationLift_lift f), fun h g hg ↦ ?_⟩
  rwa [isNormalizationLift_unique f hg (isNormalizationLift_lift f)]

/-- The compact normalized-PCF predicate is the development's. -/
theorem isNormalizedPCF_iff_scheme (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] :
    IsNormalizedPCF f ↔ IsNormalizedPCFOfFiniteType k s f := by
  rw [isNormalizedPCF_iff_lift, isNormalizedPCFOfFiniteType_iff_lift]
  letI := schemeGlobalNormalizationMap_isFinite X k s
  letI := charZero_stalk_of_field k s (genericPoint X)
  exact isPCF_iff_divisorDynamics_isPCF _

/-! ## Restrictions to point closures -/

/-- A restriction of an endomorphism to the reduced closure of an invariant point exists. -/
theorem exists_pointClosure_restriction {X : Scheme.{u}} (F : X ⟶ X) (y : X) (hy : F y = y) :
    ∃ h : pointClosure y ⟶ pointClosure y, h ≫ pointClosureι y = pointClosureι y ≫ F :=
  ⟨pointClosureSubschemeMap F y y hy, pointClosureSubschemeMap_subschemeι F y y hy⟩

/-- Transport along the unique restriction to a point closure. -/
theorem pcfAllTheWayDownAtDepth_transport {X : Scheme.{u}} (F : X ⟶ X) (y' y : X)
    (e : y' = y) (hy : F y' = y') (d : ℕ)
    (H : PCFAllTheWayDownAtDepth d (pointClosureSubschemeMap F y' y' hy))
    (g : pointClosure y ⟶ pointClosure y)
    (hg : g ≫ pointClosureι y = pointClosureι y ≫ F) :
    PCFAllTheWayDownAtDepth d g := by
  subst e
  have : g = (pointClosureSubschemeMap F y' y' hy : pointClosure y' ⟶ pointClosure y') :=
    (cancel_mono (pointClosureι y')).mp
      (hg.trans (pointClosureSubschemeMap_subschemeι F y' y' hy).symm)
  subst this
  exact H

/-- The development's recursive predicate implies the compact one. -/
theorem pcfAllTheWayDownAtDepth_of_scheme (k : Type u) [Field k] [CharZero k] (d : ℕ) :
    ∀ {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
      (f : X ⟶ X) [IsFinite f] [IsDominant f]
      [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X],
      SchemePCFAllTheWayDownAtDepth k d s f → PCFAllTheWayDownAtDepth d f := by
  induction d with
  | zero =>
      intro X s _ f _ _ _ _ _ h
      exact (isNormalizedPCF_iff_scheme k s f).mpr h
  | succ d ih =>
      intro X s _ f _ _ _ _ _ h
      refine ⟨(isNormalizedPCF_iff_scheme k s f).mpr h.1, ?_⟩
      rintro y ⟨x, r, hx, rfl⟩ p hp hper g hg
      let A : SchemeDivisorPoint X := ⟨x, hx⟩
      have hA : (End.of f ^ (r + p)).asHom A.1 = (End.of f ^ r).asHom A.1 := by
        rw [endPow_apply, endPow_apply, add_comm, Function.iterate_add_apply, hper]
      have hrec := ih _ _ (h.2 A r p hp hA)
      have hB : (schemeDivisorIterateOfFiniteType k s f r A).1 = (⇑f)^[r] x := by
        rw [schemeDivisorIterateOfFiniteType_val, endPow_apply]
      exact pcfAllTheWayDownAtDepth_transport _ _ _ hB _ d hrec g
        (by rw [hg, iterateHom_eq_pow])

/-- The compact recursive predicate implies the development's. -/
theorem schemeAtDepth_of_pcfAllTheWayDownAtDepth (k : Type u) [Field k] [CharZero k] (d : ℕ) :
    ∀ {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
      (f : X ⟶ X) [IsFinite f] [IsDominant f]
      [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X],
      PCFAllTheWayDownAtDepth d f → SchemePCFAllTheWayDownAtDepth k d s f := by
  induction d with
  | zero =>
      intro X s _ f _ _ _ _ _ h
      exact (isNormalizedPCF_iff_scheme k s f).mp h
  | succ d ih =>
      intro X s _ f _ _ _ _ _ h
      refine ⟨(isNormalizedPCF_iff_scheme k s f).mp h.1, ?_⟩
      intro A r p hp hA
      have hB : (schemeDivisorIterateOfFiniteType k s f r A).1 = (⇑f)^[r] A.1 := by
        rw [schemeDivisorIterateOfFiniteType_val, endPow_apply]
      have hper : (⇑f)^[p] (schemeDivisorIterateOfFiniteType k s f r A).1 =
          (schemeDivisorIterateOfFiniteType k s f r A).1 := by
        rw [hB, ← Function.iterate_add_apply, add_comm, ← endPow_apply, hA, endPow_apply]
      apply ih
      refine h.2 _ ⟨A.1, r, A.2, hB.symm⟩ p hp hper _ ?_
      rw [iterateHom_eq_pow]
      exact pointClosureSubschemeMap_subschemeι _ _ _ _

/-- The compact recursive predicate is the development's. -/
theorem pcfAllTheWayDownAtDepth_iff_scheme (k : Type u) [Field k] [CharZero k] (d : ℕ)
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] :
    PCFAllTheWayDownAtDepth d f ↔ SchemePCFAllTheWayDownAtDepth k d s f :=
  ⟨schemeAtDepth_of_pcfAllTheWayDownAtDepth k d s f, pcfAllTheWayDownAtDepth_of_scheme k d s f⟩

/-- The compact conclusion is the development's `SchemePCFAllTheWayDown`. -/
theorem pcfAllTheWayDown_iff_scheme (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] :
    PCFAllTheWayDown f ↔ SchemePCFAllTheWayDown k s f :=
  forall_congr' fun d ↦ pcfAllTheWayDownAtDepth_iff_scheme k d s f

end

end Pcf.Palomar
