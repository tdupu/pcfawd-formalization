/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import PaperCharPStatement
public import Pcf.Palomar.Bridge
public import Pcf.Bounding.TheoremAWeightedDownstairs
public import Pcf.Bounding.SchemePrimeToPMonodromy

/-!
# Bridge from the `paper-p.tex` statement surface to the development

The notions of `PaperCharPStatement` agree with the development's, in any
characteristic:

* `val_image_postcriticalSet`: the weighted post-critical set of a finite dominant
  endomorphism of a normal integral scheme is the set of points of the postcritical
  divisors of the development's weighted divisor dynamics;
* `isWeightedNormalizedPCF_iff_downstairs`: `IsWeightedNormalizedPCF f ↔
  Pcf.IsWeightedNormalizedPCFDownstairs k s f`;
* `isGenericallySeparable_iff`: `IsGenericallySeparable f ↔ Pcf.IsGenericallySeparable f`;
* `isSeparablePCF_iff`: `IsSeparablePCF f ↔ Pcf.IsSeparableNormalizedPCF k s f`;
* `hasPrimeToPMonodromy_iff`: the stated monodromy condition is the development's
  certificate-based `Pcf.IsPrimeToPMonodromyMap`;
* `isPCFAllSubvarietiesAtDepth_iff_scheme`, `isPCFAllSubvarieties_iff_scheme`: the stated
  recursion is the development's `Pcf.IsPCFAllSubvarieties`, with every restriction square
  transported to the development's actual return map.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

open Pcf.Palomar

namespace PaperCharP.Palomar

noncomputable section

set_option linter.style.haveILetI false

/-! ## The weighted post-critical set -/

theorem weightedIndexAt_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (d : Pcf.SchemeDivisorPoint X) :
    weightedIndexAt f d.1 = Pcf.schemeDivisorDelta f d :=
  rfl

theorem deltaDynamics_step_iterate_val {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsLocallyNoetherian X] [Pcf.IsNormalScheme X]
    (n : ℕ) (d : Pcf.SchemeDivisorPoint X) :
    ((Pcf.schemeDeltaDynamicsOfFiniteDominantNormal f).step^[n] d).1 = (⇑f)^[n] d.1 := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply]
      rfl

/-- The weighted post-critical set is the set of points of the development's weighted
postcritical divisors. -/
theorem val_image_postcriticalSet {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsLocallyNoetherian X] [Pcf.IsNormalScheme X] :
    Subtype.val '' (Pcf.schemeDeltaDynamicsOfFiniteDominantNormal f).postcriticalSet =
      weightedPostcriticalSet f := by
  let D := Pcf.schemeDeltaDynamicsOfFiniteDominantNormal f
  have hmem (Q : Pcf.SchemeDivisorPoint X) : Q ∈ D.postcriticalSet ↔
      ∃ n : ℕ, ∃ Q' : Pcf.SchemeDivisorPoint X, 1 < D.delta Q' ∧ D.step^[n] (D.step Q') = Q := by
    change Q ∈ ⋃ n : ℕ, D.step^[n] '' (D.step '' {d | 1 < D.delta d}) ↔ _
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, _, ⟨Q', hQ', rfl⟩, rfl⟩
      exact ⟨n, Q', hQ', rfl⟩
    · rintro ⟨n, Q', hQ', rfl⟩
      exact ⟨n, _, ⟨Q', hQ', rfl⟩, rfl⟩
  ext y
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    obtain ⟨n, Q', hQ', rfl⟩ := (hmem Q).mp hQ
    refine ⟨Q'.1, Q'.2, hQ', n, ?_⟩
    rw [deltaDynamics_step_iterate_val, Function.iterate_succ_apply]
    rfl
  · rintro ⟨x, hx, hδ, n, rfl⟩
    let Q' : Pcf.SchemeDivisorPoint X := ⟨x, hx⟩
    refine ⟨D.step^[n] (D.step Q'), (hmem _).mpr ⟨n, Q', hδ, rfl⟩, ?_⟩
    rw [deltaDynamics_step_iterate_val, Function.iterate_succ_apply]
    rfl

/-- The stated normalized weighted PCF predicate is the development's downstairs one. -/
theorem isWeightedNormalizedPCF_iff_downstairs (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] :
    IsWeightedNormalizedPCF f ↔ Pcf.IsWeightedNormalizedPCFDownstairs k s f := by
  letI : IsFinite (normalizationMap X) := Pcf.schemeGlobalNormalizationMap_isFinite X k s
  have hlift : IsWeightedNormalizedPCF f ↔
      (⇑(normalizationMap X) '' weightedPostcriticalSet (Pcf.schemeGlobalNormalizationLift f)).Finite :=
    ⟨fun h ↦ h _ (isNormalizationLift_lift f), fun h g hg ↦ by
      rwa [isNormalizationLift_unique f hg (isNormalizationLift_lift f)]⟩
  refine hlift.trans ?_
  rw [← val_image_postcriticalSet]
  unfold Pcf.IsWeightedNormalizedPCFDownstairs
  exact Iff.of_eq (congrArg Set.Finite (Set.image_image _ _ _))

/-! ## Separability and monodromy -/

/-- The stated generic separability is the development's. -/
theorem isGenericallySeparable_iff {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ X)
    [IsDominant f] :
    IsGenericallySeparable f ↔ Pcf.IsGenericallySeparable f :=
  Iff.rfl

/-- The stated node predicate is the development's `IsSeparableNormalizedPCF`. -/
theorem isSeparablePCF_iff (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] :
    IsSeparablePCF f ↔ Pcf.IsSeparableNormalizedPCF k s f := by
  rw [Pcf.isSeparableNormalizedPCF_iff_downstairs, IsSeparablePCF,
    isGenericallySeparable_iff, isWeightedNormalizedPCF_iff_downstairs k s f]

/-- A finite separable extension whose normal closure in an algebraic closure has degree
prime to `p` has the development's certificate-based prime-to-`p` monodromy. -/
theorem isPrimeToPMonodromy_of_normalClosure (p : ℕ) (F L : Type u) [Field F] [Field L]
    [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
    (h : (Module.finrank F
      (IntermediateField.normalClosure F L (AlgebraicClosure L))).Coprime p) :
    Pcf.IsPrimeToPMonodromy.{u, u, u} p F L :=
  Pcf.isPrimeToPMonodromy_of_embedding_into_galois p F L
    (IntermediateField.normalClosure F L (AlgebraicClosure L))
    ((normalClosure.algHomEquiv F L (AlgebraicClosure L)).symm
      (IsScalarTower.toAlgHom F L (AlgebraicClosure L))) h

/-- The stated monodromy condition implies the development's. -/
theorem isPrimeToPMonodromyMap_of_hasPrimeToPMonodromy (p : ℕ) {X : Scheme.{u}}
    [IsIntegral X] (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (h : HasPrimeToPMonodromy p f) : Pcf.IsPrimeToPMonodromyMap p f := by
  obtain ⟨hF, hfin, hsep, hcop⟩ := h
  letI := hF.toField
  letI := (f.stalkMap (genericPoint X)).hom.toAlgebra
  unfold Pcf.IsPrimeToPMonodromyMap
  exact isPrimeToPMonodromy_of_normalClosure p _ _ hcop

/-- Conversely, the development's certificate-based prime-to-`p` monodromy gives a finite
separable extension whose normal closure in an algebraic closure has degree prime to `p`. -/
theorem normalClosure_of_isPrimeToPMonodromy (p : ℕ) (F L : Type u) [Field F] [Field L]
    [Algebra F L] (h : Pcf.IsPrimeToPMonodromy.{u, u, u} p F L) :
    FiniteDimensional F L ∧ Algebra.IsSeparable F L ∧
      (Module.finrank F
        (IntermediateField.normalClosure F L (AlgebraicClosure L))).Coprime p := by
  obtain ⟨C⟩ := h
  haveI := C.finite_extension
  haveI : Nonempty (L →ₐ[F] AlgebraicClosure L) := ⟨IsScalarTower.toAlgHom F L _⟩
  refine ⟨C.finite_extension, C.separable, ?_⟩
  rw [← (IsNormalClosure.equiv (F := F) (K := L) (L := C.Closure)
    (L' := IntermediateField.normalClosure F L (AlgebraicClosure L))).toLinearEquiv.finrank_eq]
  exact C.coprimeDegree

/-- The stated monodromy condition is the development's. -/
theorem hasPrimeToPMonodromy_iff (p : ℕ) {X : Scheme.{u}}
    [IsIntegral X] (f : X ⟶ X) [IsFinite f] [IsDominant f] :
    HasPrimeToPMonodromy p f ↔ Pcf.IsPrimeToPMonodromyMap p f := by
  refine ⟨isPrimeToPMonodromyMap_of_hasPrimeToPMonodromy p f, fun h ↦ ?_⟩
  have hF : IsField (X.presheaf.stalk (f (genericPoint X))) :=
    (X.presheaf.stalkCongr (Inseparable.of_eq
      (Pcf.map_genericPoint_eq_of_isDominant f))).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField _)
  letI := hF.toField
  letI := (f.stalkMap (genericPoint X)).hom.toAlgebra
  unfold Pcf.IsPrimeToPMonodromyMap at h
  exact ⟨hF, normalClosure_of_isPrimeToPMonodromy p _ _ h⟩

/-! ## PCF on all subvarieties -/

/-- Transport along the unique restriction to a point closure. -/
theorem isPCFAllSubvarietiesAtDepth_transport {X : Scheme.{u}} (F : X ⟶ X) (y' y : X)
    (e : y' = y) (hy : F y' = y') (d : ℕ)
    (H : IsPCFAllSubvarietiesAtDepth d (Pcf.pointClosureSubschemeMap F y' y' hy))
    (g : pointClosure y ⟶ pointClosure y)
    (hg : g ≫ pointClosureι y = pointClosureι y ≫ F) :
    IsPCFAllSubvarietiesAtDepth d g := by
  subst e
  have : g = (Pcf.pointClosureSubschemeMap F y' y' hy : pointClosure y' ⟶ pointClosure y') :=
    (cancel_mono (pointClosureι y')).mp
      (hg.trans (Pcf.pointClosureSubschemeMap_subschemeι F y' y' hy).symm)
  subst this
  exact H

theorem schemePointIterate_eq {X : Scheme.{u}} (f : X ⟶ X) (n : ℕ) (x : X) :
    Pcf.schemePointIterate f n x = (⇑f)^[n] x :=
  endPow_apply f n x

/-- The development's recursive predicate implies the stated one. -/
theorem isPCFAllSubvarietiesAtDepth_of_scheme (k : Type u) [Field k] (d : ℕ) :
    ∀ {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
      (f : X ⟶ X) [IsFinite f] [IsDominant f]
      [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X],
      Pcf.IsPCFAllSubvarietiesAtDepth k d s f → IsPCFAllSubvarietiesAtDepth d f := by
  induction d with
  | zero =>
      intro X s _ f _ _ _ _ _ h
      exact (isSeparablePCF_iff k s f).mpr h
  | succ d ih =>
      intro X s _ f _ _ _ _ _ h
      refine ⟨(isSeparablePCF_iff k s f).mpr h.1, ?_⟩
      intro x hx r p hp hper g hg
      have hperiodic : Pcf.schemePointIterate f (r + p) x = Pcf.schemePointIterate f r x := by
        rw [schemePointIterate_eq, schemePointIterate_eq, hper]
      have hrec := ih _ _ (h.2 ⟨x, hx⟩ r p hp hperiodic)
      exact isPCFAllSubvarietiesAtDepth_transport _ _ _ (schemePointIterate_eq f r x)
        (Pcf.schemePointIterate_periodic f r p x hperiodic) d hrec g
        (by rw [hg, iterateHom_eq_pow])

/-- The stated recursive predicate implies the development's. -/
theorem scheme_of_isPCFAllSubvarietiesAtDepth (k : Type u) [Field k] (d : ℕ) :
    ∀ {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
      (f : X ⟶ X) [IsFinite f] [IsDominant f]
      [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X],
      IsPCFAllSubvarietiesAtDepth d f → Pcf.IsPCFAllSubvarietiesAtDepth k d s f := by
  induction d with
  | zero =>
      intro X s _ f _ _ _ _ _ h
      exact (isSeparablePCF_iff k s f).mp h
  | succ d ih =>
      intro X s _ f _ _ _ _ _ h
      refine ⟨(isSeparablePCF_iff k s f).mp h.1, ?_⟩
      intro C r p hp hperiodic
      have hper : (⇑f)^[r + p] C.1 = (⇑f)^[r] C.1 := by
        rw [← schemePointIterate_eq, ← schemePointIterate_eq, hperiodic]
      have key : ∀ (y : X), Pcf.schemePointIterate f r C.1 = y →
          (∀ g : pointClosure y ⟶ pointClosure y,
            g ≫ pointClosureι y = pointClosureι y ≫ iterateHom f p →
              IsPCFAllSubvarietiesAtDepth d g) →
          IsPCFAllSubvarietiesAtDepth d (Pcf.eventuallyPeriodicPointReturn f r p C.1 hperiodic) := by
        rintro y rfl H
        apply H
        rw [iterateHom_eq_pow]
        exact Pcf.pointClosureSubschemeMap_subschemeι _ _ _
          (Pcf.schemePointIterate_periodic f r p C.1 hperiodic)
      apply ih
      exact key _ (schemePointIterate_eq f r C.1) (h.2 C.1 C.2 r p hp hper)

/-- The stated finite-depth recursion is the development's. -/
theorem isPCFAllSubvarietiesAtDepth_iff_scheme (k : Type u) [Field k] (d : ℕ)
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] :
    IsPCFAllSubvarietiesAtDepth d f ↔ Pcf.IsPCFAllSubvarietiesAtDepth k d s f :=
  ⟨scheme_of_isPCFAllSubvarietiesAtDepth k d s f, isPCFAllSubvarietiesAtDepth_of_scheme k d s f⟩

/-- The stated conclusion is the development's `Pcf.IsPCFAllSubvarieties`. -/
theorem isPCFAllSubvarieties_iff_scheme (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] :
    IsPCFAllSubvarieties f ↔ Pcf.IsPCFAllSubvarieties k s f :=
  forall_congr' fun d ↦ isPCFAllSubvarietiesAtDepth_iff_scheme k d s f

end

end PaperCharP.Palomar
