/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllSubvarietyFiniteCoverInputAlignment

/-!
# Normal schemes and their integral closures

The normal-scheme comparison needed to identify normalized PCF with the
paper's ordinary normal non-étale PCF starts with two local facts: each
normal affine coordinate ring is already its own integral closure in its
fraction field, and every local ring of a normal scheme is integrally
closed. These are proved here on the actual rings and stalks.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

set_option linter.style.haveILetI false

/-- An integrally closed domain coincides with its integral closure in
any of its fraction fields. -/
noncomputable def integrallyClosed_equiv_integralClosure
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K] :
    R ≃+* integralClosure R K := by
  let φ := algebraMap R (integralClosure R K)
  have hinj : Function.Injective φ := by
    intro x y hxy
    apply IsFractionRing.injective R K
    exact congrArg Subtype.val hxy
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral x.property
    exact ⟨r, Subtype.ext hr⟩
  exact RingEquiv.ofBijective φ ⟨hinj, hsurj⟩

/-- Normality of all affine coordinate rings implies that every actual
local ring of the scheme is integrally closed. -/
theorem IsNormalScheme.stalk_integrallyClosed
    (X : Scheme.{u}) [IsIntegral X] [IsNormalScheme X] (x : X) :
    IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  let xU : U := ⟨x, hxU⟩
  let : IsIntegrallyClosed Γ(X, U) :=
    IsNormalScheme.component_integrallyClosed ⟨U, hU⟩
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk _ xU
  let : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf xU).asIdeal := hU.isLocalization_stalk xU
  exact isIntegrallyClosed_of_isLocalization _ _
    (hU.primeIdealOf xU).asIdeal.primeCompl_le_nonZeroDivisors

/-- Over an affine open of a normal integral scheme, the normalization
map is an isomorphism on sections: the integral-closure ring is the
original coordinate ring. -/
theorem normalScheme_normalizationMap_app_isIso
    (X : Scheme.{u}) [IsIntegral X] [IsNormalScheme X]
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsIso ((Palomar.normalizationMap X).app U) := by
  let f := schemeGenericInclusion X
  letI : Algebra Γ(X, U) Γ(Spec X.functionField, f ⁻¹ᵁ U) :=
    (f.app U).hom.toAlgebra
  by_cases hne : Nonempty U
  · have hgeneric : genericPoint X ∈ U :=
      ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hne)
    have htop : f ⁻¹ᵁ U = ⊤ :=
      Scheme.preimage_eq_top_of_closedPoint_mem f (by simpa [f, schemeGenericInclusion])
    let e : Γ(Spec X.functionField, f ⁻¹ᵁ U) ≅ X.functionField :=
      (Spec X.functionField).presheaf.mapIso (eqToIso htop.symm).op ≪≫
        Scheme.ΓSpecIso X.functionField
    have he : f.app U ≫ e.hom = X.germToFunctionField U := by
      dsimp [f, schemeGenericInclusion, e]
      rw [Scheme.fromSpecStalk_app hgeneric]
      simp only [Category.assoc, ← Functor.map_comp_assoc]
      simp
    let ea : Γ(Spec X.functionField, f ⁻¹ᵁ U) ≃ₐ[Γ(X, U)] X.functionField :=
      { e.commRingCatIsoToRingEquiv with
        commutes' r := congr($(he) r) }
    letI : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    letI : Field Γ(Spec X.functionField, f ⁻¹ᵁ U) :=
      ((MulEquiv.isField_congr e.commRingCatIsoToRingEquiv.toMulEquiv).mpr
        (Field.toIsField X.functionField)).toField
    letI : IsFractionRing Γ(X, U)
        Γ(Spec X.functionField, f ⁻¹ᵁ U) :=
      IsFractionRing.of_algEquiv ea.symm
    letI : IsIntegrallyClosed Γ(X, U) :=
      IsNormalScheme.component_integrallyClosed ⟨U, hU⟩
    have hiso : IsIso (CommRingCat.ofHom
        (algebraMap Γ(X, U)
          (integralClosure Γ(X, U) Γ(Spec X.functionField, f ⁻¹ᵁ U)))) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr
        (integrallyClosed_equiv_integralClosure Γ(X, U)
          Γ(Spec X.functionField, f ⁻¹ᵁ U)).bijective
    change IsIso (f.fromNormalization.app U)
    rw [f.fromNormalization_app hU]
    infer_instance
  · have hbot : U = ⊥ := by
      ext x
      exact ⟨fun hx ↦ (hne ⟨⟨x, hx⟩⟩).elim, fun hx ↦ hx.elim⟩
    subst U
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have hdom : Subsingleton Γ(X, (⊥ : X.Opens)) := inferInstance
    have hcod : Subsingleton Γ(Palomar.normalization X,
        Palomar.normalizationMap X ⁻¹ᵁ ⊥) := by
      simpa only [Scheme.Hom.preimage_bot] using
        (inferInstance : Subsingleton Γ(Palomar.normalization X, ⊥))
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ y⟩⟩

/-- The canonical absolute normalization of a normal integral scheme is
an isomorphism. -/
theorem normalScheme_normalizationMap_isIso
    (X : Scheme.{u}) [IsIntegral X] [IsNormalScheme X] :
    IsIso (Palomar.normalizationMap X) := by
  let U (i : X) : X.Opens := by
    letI : IsOpenImmersion (X.affineCover.f i) := X.affineCover.map_prop i
    exact (X.affineCover.f i).opensRange
  have hcover : iSup U = ⊤ := by
    change ⨆ i, (X.affineCover.f i).opensRange = ⊤
    exact X.affineCover.iSup_opensRange
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := .isomorphisms _) U hcover).mpr fun i ↦ ?_
  letI : IsOpenImmersion (X.affineCover.f i) := X.affineCover.map_prop i
  have hU : IsAffineOpen (U i) := isAffineOpen_opensRange (X.affineCover.f i)
  exact (isIso_morphismRestrict_iff_isIso_app (Palomar.normalizationMap X) hU).mpr
    (normalScheme_normalizationMap_app_isIso X (U i) hU)

/-- On a normal scheme, the actual canonical lift is the conjugate of the
original map by its canonical normalization isomorphism. -/
theorem normalScheme_normalizationLift_eq_conjugate
    {X : Scheme.{u}} [IsIntegral X] [IsNormalScheme X]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] :
    letI : IsIso (Palomar.normalizationMap X) :=
      normalScheme_normalizationMap_isIso X
    schemeGlobalNormalizationLift f =
      Palomar.normalizationMap X ≫ f ≫ inv (Palomar.normalizationMap X) := by
  letI : IsIso (Palomar.normalizationMap X) :=
    normalScheme_normalizationMap_isIso X
  calc
    schemeGlobalNormalizationLift f =
        (schemeGlobalNormalizationLift f ≫ Palomar.normalizationMap X) ≫
          inv (Palomar.normalizationMap X) := by simp
    _ = Palomar.normalizationMap X ≫ f ≫
          inv (Palomar.normalizationMap X) := by
      rw [schemeGlobalNormalizationLift_comp]
      simp only [Category.assoc]

/-- At each actual point of a normal scheme, the stalk map of the
canonical lift is formally étale exactly when the original stalk map is.
The identification uses the normalization square and its isomorphism on
both local rings. -/
theorem normalScheme_formallyEtale_normalizationLift_iff
    {X : Scheme.{u}} [IsIntegral X] [IsNormalScheme X]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (x : Palomar.normalization X) :
    ((schemeGlobalNormalizationLift f).stalkMap x).hom.FormallyEtale ↔
      (f.stalkMap ((Palomar.normalizationMap X) x)).hom.FormallyEtale := by
  let N := Palomar.normalization X
  let ν := Palomar.normalizationMap X
  let l := schemeGlobalNormalizationLift f
  letI : IsIso ν := normalScheme_normalizationMap_isIso X
  have hi₁ : IsIso (ν.stalkMap x) :=
    (isIso_iff_isIso_stalkMap ν).mp inferInstance |>.2 x
  have hi₂ : IsIso (ν.stalkMap (l x)) :=
    (isIso_iff_isIso_stalkMap ν).mp inferInstance |>.2 (l x)
  calc
    (l.stalkMap x).hom.FormallyEtale ↔
        ((l ≫ ν).stalkMap x).hom.FormallyEtale := by
      rw [Scheme.Hom.stalkMap_comp]
      exact (formallyEtale_respectsIso.cancel_left_isIso _ _).symm
    _ ↔ ((ν ≫ f).stalkMap x).hom.FormallyEtale := by
      rw [schemeGlobalNormalizationLift_comp]
    _ ↔ (f.stalkMap (ν x)).hom.FormallyEtale := by
      rw [Scheme.Hom.stalkMap_comp]
      exact formallyEtale_respectsIso.cancel_right_isIso _ _

/-- On codimension-one points, the actual non-étale locus of the
normalization lift is exactly the inverse image of the original locus
under the divisor map of the canonical normalization isomorphism. -/
theorem normalScheme_nonEtaleLocus_normalizationLift_iff
    {X : Scheme.{u}} [IsIntegral X] [IsNormalScheme X]
    [IsLocallyNoetherian X]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (Q : SchemeDivisorPoint (Palomar.normalization X)) :
    letI : IsFinite (Palomar.normalizationMap X) := by
      letI : IsIso (Palomar.normalizationMap X) :=
        normalScheme_normalizationMap_isIso X
      infer_instance
    Q ∈ schemeDivisorNonEtaleLocus (schemeGlobalNormalizationLift f) ↔
      Q.mapFiniteDominantNormal (Palomar.normalizationMap X) ∈
        schemeDivisorNonEtaleLocus f := by
  letI : IsIso (Palomar.normalizationMap X) :=
    normalScheme_normalizationMap_isIso X
  letI : IsFinite (Palomar.normalizationMap X) := inferInstance
  change ¬ ((schemeGlobalNormalizationLift f).stalkMap Q.1).hom.FormallyEtale ↔
    ¬ (f.stalkMap ((Palomar.normalizationMap X) Q.1)).hom.FormallyEtale
  exact not_congr (normalScheme_formallyEtale_normalizationLift_iff f Q.1)

/-- The non-étale postcritical set is invariant under an exact conjugacy
of divisor dynamics. Only the first non-étale locus is needed by the
definition of postcritical finiteness. -/
theorem UnnormalizedDynamics.isNonEtaleBranchPCF_iff_of_equiv
    {P : Type u} {Q : Type v}
    (D : UnnormalizedDynamics P) (E : UnnormalizedDynamics Q)
    (e : P ≃ Q)
    (hstep : Function.Semiconj e D.step E.step)
    (hcrit : e '' D.nonEtaleLocus 1 = E.nonEtaleLocus 1) :
    D.IsNonEtaleBranchPCF ↔ E.IsNonEtaleBranchPCF := by
  have himage (n : ℕ) (S : Set P) :
      e '' (D.step^[n] '' S) = E.step^[n] '' (e '' S) := by
    rw [← Set.image_comp, ← Set.image_comp]
    congr 1
    funext x
    exact (hstep.iterate_right n) x
  have hbranch : e '' D.nonEtaleBranch 1 = E.nonEtaleBranch 1 := by
    change e '' (D.step^[1] '' D.nonEtaleLocus 1) =
      E.step^[1] '' E.nonEtaleLocus 1
    rw [himage, hcrit]
  have hpost : e '' D.nonEtalePostcriticalSet = E.nonEtalePostcriticalSet := by
    change e '' (⋃ n : ℕ, D.step^[n] '' D.nonEtaleBranch 1) =
      ⋃ n : ℕ, E.step^[n] '' E.nonEtaleBranch 1
    rw [Set.image_iUnion]
    simp_rw [himage, hbranch]
  change D.nonEtalePostcriticalSet.Finite ↔ E.nonEtalePostcriticalSet.Finite
  rw [← hpost]
  exact (Set.finite_image_iff e.injective.injOn).symm

/-- The canonical normalization isomorphism induces an equivalence on
the actual codimension-one scheme points. -/
noncomputable def normalScheme_normalizationDivisorEquiv
    (X : Scheme.{u}) [IsIntegral X] [IsNormalScheme X]
    [IsLocallyNoetherian X] :
    SchemeDivisorPoint (Palomar.normalization X) ≃ SchemeDivisorPoint X := by
  let ν := Palomar.normalizationMap X
  letI : IsIso ν := normalScheme_normalizationMap_isIso X
  letI : IsFinite ν := inferInstance
  apply Equiv.ofBijective
    (fun Q : SchemeDivisorPoint (Palomar.normalization X) ↦
      Q.mapFiniteDominantNormal ν)
  constructor
  · intro Q R h
    apply Subtype.ext
    exact (ConcreteCategory.bijective_of_isIso ν.base).injective
      (congrArg Subtype.val h)
  · exact SchemeDivisorPoint.mapFiniteDominantNormal_surjective ν

/-- Non-étale PCF of a finite generically separable self-map on a normal
scheme agrees with that of its actual canonical normalization lift. -/
theorem normalScheme_isNormalNonEtalePCF_lift_iff
    {X : Scheme.{u}} [IsIntegral X] [IsNormalScheme X]
    [IsLocallyNoetherian X] [NoetherianSpace X]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hsep : IsGenericallySeparable f) :
    letI : IsFinite (Palomar.normalizationMap X) := by
      letI : IsIso (Palomar.normalizationMap X) :=
        normalScheme_normalizationMap_isIso X
      infer_instance
    IsNormalNonEtalePCF (schemeGlobalNormalizationLift f)
      (isGenericallySeparable_schemeGlobalNormalizationLift f hsep) ↔
      IsNormalNonEtalePCF f hsep := by
  let ν := Palomar.normalizationMap X
  let l := schemeGlobalNormalizationLift f
  letI : IsIso ν := normalScheme_normalizationMap_isIso X
  letI : IsFinite ν := inferInstance
  let e := normalScheme_normalizationDivisorEquiv X
  let D := unnormalizedDynamicsOfFiniteDominantNormalSeparable l
    (isGenericallySeparable_schemeGlobalNormalizationLift f hsep)
  let E := unnormalizedDynamicsOfFiniteDominantNormalSeparable f hsep
  have hstep : Function.Semiconj e D.step E.step := by
    intro Q
    apply Subtype.ext
    change ν (l Q.1) = f (ν Q.1)
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun h : Palomar.normalization X ⟶ X ↦ h Q.1)
        (schemeGlobalNormalizationLift_comp f)
  have hcritpoint (Q : SchemeDivisorPoint (Palomar.normalization X)) :
      Q ∈ D.nonEtaleLocus 1 ↔ e Q ∈ E.nonEtaleLocus 1 := by
    change Q ∈ schemeDivisorNonEtaleLocus (End.of l ^ 1).asHom ↔
      Q.mapFiniteDominantNormal ν ∈
        schemeDivisorNonEtaleLocus (End.of f ^ 1).asHom
    simpa only [pow_one] using
      (normalScheme_nonEtaleLocus_normalizationLift_iff f Q)
  have hcrit : e '' D.nonEtaleLocus 1 = E.nonEtaleLocus 1 := by
    ext P
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      exact (hcritpoint Q).mp hQ
    · intro hP
      obtain ⟨Q, rfl⟩ := e.surjective P
      exact ⟨Q, (hcritpoint Q).mpr hP, rfl⟩
  exact D.isNonEtaleBranchPCF_iff_of_equiv E e hstep hcrit

/-- For a normal integral finite-type scheme, the characteristic-free
normalized predicate is exactly generic separability together with the
paper's actual normal non-étale PCF predicate. The structure map to the
field only supplies normalization finiteness. -/
theorem normalScheme_isSeparableNormalizedPCF_iff
    (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsNormalScheme X]
    [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] :
    IsSeparableNormalizedPCF k s f ↔
      ∃ hsep : IsGenericallySeparable f, IsNormalNonEtalePCF f hsep := by
  rw [isSeparableNormalizedPCF_iff_normalLift k s f]
  constructor
  · rintro ⟨hsep, hpcf⟩
    exact ⟨hsep, (normalScheme_isNormalNonEtalePCF_lift_iff f hsep).mp hpcf⟩
  · rintro ⟨hsep, hpcf⟩
    exact ⟨hsep, (normalScheme_isNormalNonEtalePCF_lift_iff f hsep).mpr hpcf⟩

#print axioms integrallyClosed_equiv_integralClosure
#print axioms IsNormalScheme.stalk_integrallyClosed
#print axioms normalScheme_normalizationMap_app_isIso
#print axioms normalScheme_normalizationMap_isIso
#print axioms normalScheme_normalizationLift_eq_conjugate
#print axioms normalScheme_formallyEtale_normalizationLift_iff
#print axioms normalScheme_nonEtaleLocus_normalizationLift_iff
#print axioms UnnormalizedDynamics.isNonEtaleBranchPCF_iff_of_equiv
#print axioms normalScheme_normalizationDivisorEquiv
#print axioms normalScheme_isNormalNonEtalePCF_lift_iff
#print axioms normalScheme_isSeparableNormalizedPCF_iff

end Pcf
