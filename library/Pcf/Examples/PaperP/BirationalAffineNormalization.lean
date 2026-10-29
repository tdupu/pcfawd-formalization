/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.CuspAbsoluteNormalization
public import Pcf.Bounding.TheoremAWeightedDownstairs
public import Pcf.Bounding.SchemePurelyInseparableDelta

/-!
# Absolute normalization of an affine domain with a birational finite cover

Let `R → S` be a finite injective map of domains whose fraction fields agree
(`FractionRing S` is a fraction ring of `R`), with `S` integrally closed.
Then the library's absolute normalization `Palomar.normalization (Spec R)`
is canonically `Spec S`, over `Spec R`, and the canonical normalized lift of
`Spec S ⟶ Spec R` is an isomorphism.

This is the argument of `Pcf.Examples.PaperP.CuspAbsoluteNormalization` and
`CuspCanonicalLift` with the cusp data replaced by general hypotheses. It is
used for the nodal cubic in `paper-p.tex`, Example `ex:loci-compared`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.BirationalAffineNormalization

open AlgebraicGeometry CategoryTheory

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

variable (R S : Type u) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [IsFractionRing R (FractionRing S)]

/-- The affine scheme map induced by `R → S`. -/
noncomputable abbrev schemeMap : Spec (.of S) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R S))

instance schemeMap_isFinite : IsFinite (schemeMap R S) := by
  apply (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap R S))).mpr
  exact RingHom.finite_algebraMap.mpr inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance schemeMap_isDominant : IsDominant (schemeMap R S) := by
  have hs : Function.Surjective (PrimeSpectrum.comap (algebraMap R S)) :=
    (Algebra.IsIntegral.isIntegral (R := R) (A := S) |>
      fun _ => (RingHom.IsIntegral.comap_surjective (f := algebraMap R S)
        (fun x => Algebra.IsIntegral.isIntegral x)
        (FaithfulSMul.algebraMap_injective R S)))
  haveI : Surjective (schemeMap R S) := by
    constructor
    intro y
    obtain ⟨x, hx⟩ := hs y
    exact ⟨x, hx⟩
  infer_instance

instance top_nonempty : Nonempty (⊤ : (Spec (.of R)).Opens) :=
  ⟨⟨genericPoint (Spec (.of R)), trivial⟩⟩

/-- The function field of `Spec R` is a fraction ring of `R`. -/
theorem functionField_isFractionRing :
    let X := Spec (.of R)
    letI : Algebra R X.functionField :=
      ((X.germToFunctionField ⊤).hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
    IsFractionRing R X.functionField := by
  let X := Spec (.of R)
  letI : Algebra Γ(X, ⊤) X.functionField := (X.germToFunctionField ⊤).hom.toAlgebra
  letI : Algebra R X.functionField :=
    ((X.germToFunctionField ⊤).hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  letI : IsFractionRing Γ(X, ⊤) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X ⊤ (isAffineOpen_top X)
  apply IsFractionRing.of_ringEquiv_left
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm
  intro c
  rfl

/-- The function field of `Spec R` is canonically `Frac S`, over `R`. -/
noncomputable def functionFieldEquiv :
    let X := Spec (.of R)
    letI : Algebra R X.functionField :=
      ((X.germToFunctionField ⊤).hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
    X.functionField ≃ₐ[R] FractionRing S := by
  let X := Spec (.of R)
  letI : Algebra R X.functionField :=
    ((X.germToFunctionField ⊤).hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  letI : IsFractionRing R X.functionField := functionField_isFractionRing R
  exact (FractionRing.algEquiv (A := R) X.functionField).symm.trans
    (FractionRing.algEquiv (A := R) (FractionRing S))

/-- The generic point of `Spec R` mapped into `Spec S`. -/
noncomputable def genericToCover :
    Spec (Spec (.of R)).functionField ⟶ Spec (.of S) := by
  let X := Spec (.of R)
  letI : Algebra R X.functionField :=
    ((X.germToFunctionField ⊤).hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  exact Spec.map (CommRingCat.ofHom
    ((functionFieldEquiv R S).symm.toRingHom.comp (algebraMap S (FractionRing S))))

set_option backward.isDefEq.respectTransparency.types false in
theorem genericToCover_comp :
    genericToCover R S ≫ schemeMap R S = Pcf.schemeGenericInclusion (Spec (.of R)) := by
  let X := Spec (.of R)
  letI : Algebra R X.functionField :=
    ((X.germToFunctionField ⊤).hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  unfold genericToCover schemeMap Pcf.schemeGenericInclusion
  rw [Spec.fromSpecStalk_eq, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change (functionFieldEquiv R S).symm
    (algebraMap S (FractionRing S) (algebraMap R S a)) =
    algebraMap R X.functionField a
  rw [← IsScalarTower.algebraMap_apply]
  exact (functionFieldEquiv R S).symm.commutes a

/-- The canonical map from the absolute normalization of `Spec R` to `Spec S`. -/
noncomputable def normalizationToCover :
    Pcf.Palomar.normalization (Spec (.of R)) ⟶ Spec (.of S) :=
  (Pcf.schemeGenericInclusion (Spec (.of R))).normalizationDesc
    (genericToCover R S) (schemeMap R S) (genericToCover_comp R S).symm

@[reassoc]
theorem normalizationToCover_comp :
    normalizationToCover R S ≫ schemeMap R S =
      Pcf.Palomar.normalizationMap (Spec (.of R)) :=
  (Pcf.schemeGenericInclusion (Spec (.of R))).normalizationDesc_comp
    (genericToCover R S) (schemeMap R S) (genericToCover_comp R S).symm

theorem genericToNormalization_normalizationToCover :
    Pcf.Palomar.genericToNormalization (Spec (.of R)) ≫ normalizationToCover R S =
      genericToCover R S :=
  (Pcf.schemeGenericInclusion (Spec (.of R))).toNormalization_normalizationDesc
    (genericToCover R S) (schemeMap R S) (genericToCover_comp R S).symm

/-- The function field of `Spec R` is a fraction field of `S`. -/
theorem cover_generic_isFractionRing :
    let K := (Spec (.of R)).functionField
    letI : Algebra R K :=
      (((Spec (.of R)).germToFunctionField ⊤).hom.comp
        (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
    letI : Algebra S K :=
      ((functionFieldEquiv R S).symm.toRingEquiv.toRingHom.comp
        (algebraMap S (FractionRing S))).toAlgebra
    IsFractionRing S K := by
  let K := (Spec (.of R)).functionField
  letI : Algebra R K :=
    (((Spec (.of R)).germToFunctionField ⊤).hom.comp
      (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  letI : Algebra S K :=
    ((functionFieldEquiv R S).symm.toRingEquiv.toRingHom.comp
      (algebraMap S (FractionRing S))).toAlgebra
  let e : FractionRing S ≃ₐ[S] K :=
    { (functionFieldEquiv R S).symm.toRingEquiv with commutes' a := rfl }
  exact IsFractionRing.of_algEquiv e

variable [IsIntegrallyClosed S]

theorem cover_generic_isIntegrallyClosedIn :
    let K := (Spec (.of R)).functionField
    let f := genericToCover R S
    letI : Algebra Γ(Spec (.of S), ⊤) Γ(Spec K, ⊤) := f.appTop.hom.toAlgebra
    IsIntegrallyClosedIn Γ(Spec (.of S), ⊤) Γ(Spec K, ⊤) := by
  let A := (.of S : CommRingCat)
  let K := (Spec (.of R)).functionField
  let f := genericToCover R S
  letI : Algebra R K :=
    (((Spec (.of R)).germToFunctionField ⊤).hom.comp
      (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  letI : Algebra A K :=
    ((functionFieldEquiv R S).symm.toRingEquiv.toRingHom.comp
      (algebraMap S (FractionRing S))).toAlgebra
  letI : IsFractionRing A K := cover_generic_isFractionRing R S
  let B := Γ(Spec A, ⊤)
  let T := Γ(Spec K, ⊤)
  letI : Algebra B T := f.appTop.hom.toAlgebra
  let φ : A ≃+* B := (Scheme.ΓSpecIso A).symm.commRingCatIsoToRingEquiv
  let ψ : T ≃+* K := (Scheme.ΓSpecIso K).commRingCatIsoToRingEquiv
  letI : Algebra A T := Algebra.compHom T φ.toRingHom
  have hcomp : (algebraMap B T).comp φ.toRingHom = algebraMap A T := rfl
  let j : A ⟶ K := CommRingCat.ofHom (algebraMap A K)
  have hf : f = Spec.map j := by
    dsimp [f, j, genericToCover]
    rfl
  have hn := Scheme.ΓSpecIso_inv_naturality j
  rw [← hf] at hn
  have hnat (r : A) : ψ ((algebraMap A T) r) = algebraMap A K r := by
    have h := congrArg (fun (z : A ⟶ T) => z.hom r) hn
    change (Scheme.ΓSpecIso K).inv.hom (algebraMap A K r) =
      f.appTop.hom ((Scheme.ΓSpecIso A).inv.hom r) at h
    change ψ (f.appTop.hom ((Scheme.ΓSpecIso A).inv.hom r)) = _
    rw [← h]
    change ψ (ψ.symm (algebraMap A K r)) = _
    exact ψ.apply_symm_apply _
  have hnat' : ψ.toRingHom.comp (algebraMap A T) = algebraMap A K := by
    apply RingHom.ext
    intro r
    exact hnat r
  have hmapinj : Function.Injective (algebraMap A T) := by
    intro a b hab
    apply (IsFractionRing.injective A K)
    rw [← hnat a, ← hnat b, hab]
  have hinj : Function.Injective (algebraMap B T) := by
    intro a b hab
    obtain ⟨a, rfl⟩ := φ.surjective a
    obtain ⟨b, rfl⟩ := φ.surjective b
    change ((algebraMap B T).comp φ.toRingHom) a =
      ((algebraMap B T).comp φ.toRingHom) b at hab
    rw [hcomp] at hab
    exact congrArg φ (hmapinj hab)
  apply (isIntegrallyClosedIn_iff).mpr
  refine ⟨hinj, ?_⟩
  intro x hx
  have hR : IsIntegral A x := (φ.isIntegral_iff hcomp x).mpr hx
  have hRK : IsIntegral A (ψ x) :=
    IsIntegral.map_of_comp_eq (RingHom.id A) ψ.toRingHom (by simpa using hnat'.symm) hR
  haveI : IsIntegrallyClosed A := inferInstanceAs (IsIntegrallyClosed S)
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff K).mp inferInstance hRK
  refine ⟨φ y, ?_⟩
  apply ψ.injective
  change ψ (((algebraMap B T).comp φ.toRingHom) y) = ψ x
  rw [hcomp, hnat y]
  exact hy

theorem genericToCover_fromNormalization_isIso :
    IsIso (genericToCover R S).fromNormalization := by
  let A := (.of S : CommRingCat)
  let K := (Spec (.of R)).functionField
  let f := genericToCover R S
  let B := Γ(Spec A, ⊤)
  let T := Γ(Spec K, f ⁻¹ᵁ (⊤ : (Spec A).Opens))
  letI : Algebra B T := (f.app ⊤).hom.toAlgebra
  have hnormal : IsIntegrallyClosedIn B T := by
    convert cover_generic_isIntegrallyClosedIn R S using 1
    rfl
  let C := integralClosure B T
  have hbij : Function.Bijective (algebraMap B C) := by
    constructor
    · intro a b h
      apply (isIntegrallyClosedIn_iff.mp hnormal).1
      exact congrArg (Subalgebra.val C) h
    · intro x
      obtain ⟨s, hs⟩ := (isIntegrallyClosedIn_iff.mp hnormal).2 x.property
      refine ⟨s, ?_⟩
      apply Subtype.ext
      exact hs
  have hTop : IsIso f.fromNormalization.appTop := by
    change IsIso (f.fromNormalization.app ⊤)
    rw [f.fromNormalization_app (isAffineOpen_top (Spec A))]
    haveI : IsIso (CommRingCat.ofHom (algebraMap B C)) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr hbij
    infer_instance
  letI : IsAffine f.normalization := isAffine_of_isAffineHom f.fromNormalization
  have hSpec : IsIso (Spec.map f.fromNormalization.appTop) := inferInstance
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _)
    (arrowIsoSpecΓOfIsAffine f.fromNormalization)).mpr hSpec

/-- Transitivity of relative normalization for a specified factorization
(copied from `CuspAbsoluteNormalization`, where it is private). -/
theorem normalizationDesc_isIso_of_factor
    {X Y Z : Scheme} (h : X ⟶ Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiSeparated f] [IsIntegralHom g]
    [QuasiCompact h] [QuasiSeparated h] [IsIso f.fromNormalization]
    (H : h = f ≫ g) : IsIso (h.normalizationDesc f g H) := by
  subst H
  exact Pcf.Stacks.normalizationDesc_isIso_of_fromNormalization_isIso f g

/-- **The absolute normalization of `Spec R` is `Spec S`**: the canonical
comparison map is an isomorphism. -/
theorem normalizationToCover_isIso : IsIso (normalizationToCover R S) := by
  letI : IsIso (genericToCover R S).fromNormalization :=
    genericToCover_fromNormalization_isIso R S
  exact normalizationDesc_isIso_of_factor
    (Pcf.schemeGenericInclusion (Spec (.of R))) (genericToCover R S) (schemeMap R S)
      (genericToCover_comp R S).symm

/-- The typed isomorphism `Palomar.normalization (Spec R) ≅ Spec S`.

`paper-p.tex` correspondence: Example A.5 (`ex:loci-compared`). -/
noncomputable def normalizationIsoCover :
    Pcf.Palomar.normalization (Spec (.of R)) ≅ Spec (.of S) :=
  letI : IsIso (normalizationToCover R S) := normalizationToCover_isIso R S
  asIso (normalizationToCover R S)

/-- The typed isomorphism is over `Spec R`. -/
@[reassoc]
theorem normalizationIsoCover_hom_comp :
    (normalizationIsoCover R S).hom ≫ schemeMap R S =
      Pcf.Palomar.normalizationMap (Spec (.of R)) :=
  normalizationToCover_comp R S

include S in
theorem normalizationMap_isFinite :
    IsFinite (Pcf.Palomar.normalizationMap (Spec (.of R))) := by
  rw [← normalizationIsoCover_hom_comp R S]
  infer_instance

theorem cover_normalizationMap_isIso :
    IsIso (Pcf.Palomar.normalizationMap (Spec (.of S))) :=
  Pcf.Stacks.genericPoint_fromNormalization_isIso (.of S)

theorem cover_normalizationMap_isFinite :
    IsFinite (Pcf.Palomar.normalizationMap (Spec (.of S))) := by
  letI := cover_normalizationMap_isIso S
  infer_instance

/-- The explicit normalized lift. -/
noncomputable def normalizedLift :
    Pcf.Palomar.normalization (Spec (.of S)) ⟶ Pcf.Palomar.normalization (Spec (.of R)) :=
  Pcf.Palomar.normalizationMap (Spec (.of S)) ≫ (normalizationIsoCover R S).inv

theorem normalizedLift_comp :
    normalizedLift R S ≫ Pcf.Palomar.normalizationMap (Spec (.of R)) =
      Pcf.Palomar.normalizationMap (Spec (.of S)) ≫ schemeMap R S := by
  unfold normalizedLift
  rw [← normalizationIsoCover_hom_comp R S]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

theorem normalizedLift_isIso : IsIso (normalizedLift R S) := by
  letI := cover_normalizationMap_isIso S
  unfold normalizedLift
  infer_instance

omit [Module.Finite R S] [FaithfulSMul R S] [IsFractionRing R (FractionRing S)]
  [IsIntegrallyClosed S] in
/-- Ring maps out of `S` into a field are determined by their restriction to
`R`, provided that restriction is injective and `S` is birational over `R`. -/
theorem ringHom_ext_of_birational {L : Type*} [Field L]
    [IsFractionRing R (FractionRing S)] {a b : S →+* L}
    (h : a.comp (algebraMap R S) = b.comp (algebraMap R S))
    (hinj : Function.Injective (a.comp (algebraMap R S))) : a = b := by
  ext s
  obtain ⟨⟨r, d⟩, hrd⟩ := IsLocalization.surj (nonZeroDivisors R)
    (algebraMap S (FractionRing S) s)
  have hd0 : (d : R) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hrel : s * algebraMap R S d = algebraMap R S r := by
    apply IsFractionRing.injective S (FractionRing S)
    simpa only [map_mul, ← IsScalarTower.algebraMap_apply] using hrd
  have hadne : a (algebraMap R S d) ≠ 0 := by
    intro h0
    apply hd0
    apply hinj
    simpa using h0
  have ha := congrArg a hrel
  have hb := congrArg b hrel
  rw [map_mul] at ha hb
  have hbr : b (algebraMap R S r) = a (algebraMap R S r) :=
    (DFunLike.congr_fun h r).symm
  have hbd : b (algebraMap R S d) = a (algebraMap R S d) :=
    (DFunLike.congr_fun h (d : R)).symm
  rw [hbr, hbd] at hb
  exact mul_right_cancel₀ hadne (ha.trans hb.symm)

set_option backward.isDefEq.respectTransparency.types false in
/-- The generic inclusion of `Spec S` factors through the generic map of the
cover followed by `genericToCover`. -/
theorem coverGenericInclusion_comp :
    Pcf.schemeGenericInclusion (Spec (.of S)) =
      Pcf.schemeGenericMorphism (schemeMap R S) ≫ genericToCover R S := by
  let Y := Spec (.of S)
  let f := Pcf.schemeGenericInclusion Y
  let g := Pcf.schemeGenericMorphism (schemeMap R S) ≫ genericToCover R S
  have h : f ≫ schemeMap R S = g ≫ schemeMap R S := by
    dsimp [f, g]
    rw [Category.assoc, genericToCover_comp, Pcf.schemeGenericMorphism_comp]
  obtain ⟨a, ha⟩ := Spec.map_surjective (R := .of S) (S := Y.functionField) f
  obtain ⟨b, hb⟩ := Spec.map_surjective (R := .of S) (S := Y.functionField) g
  have hfa : f = Spec.map a := ha.symm
  have hainj : Function.Injective a.hom := by
    have hf : f = Spec.map ((Scheme.ΓSpecIso (.of S)).inv ≫
        (Spec (.of S)).presheaf.germ ⊤ (genericPoint (Spec (.of S))) trivial) := by
      dsimp [f, Pcf.schemeGenericInclusion]
      exact Spec.fromSpecStalk_eq _ _
    have hab := Spec.map_injective (hfa.symm.trans hf)
    rw [hab]
    intro x y hxy
    apply (Scheme.ΓSpecIso (.of S)).commRingCatIsoToRingEquiv.symm.injective
    exact germ_injective_of_isIntegral (Spec (.of S)) (U := ⊤)
      (genericPoint (Spec (.of S))) trivial hxy
  change f = g
  rw [← ha, ← hb] at h ⊢
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  unfold schemeMap at h
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have h' := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  apply ringHom_ext_of_birational R S h'
  exact hainj.comp (FaithfulSMul.algebraMap_injective R S)

/-- The explicit normalized lift is the library's canonical lift. -/
theorem normalizedLift_eq_canonical :
    normalizedLift R S = Pcf.schemeGlobalNormalizationMorphism (schemeMap R S) := by
  letI : IsIso (normalizationToCover R S) := normalizationToCover_isIso R S
  apply Pcf.schemeGlobalNormalizationMorphism_unique
  · exact normalizedLift_comp R S
  · apply (cancel_mono (normalizationToCover R S)).mp
    simp only [Category.assoc]
    rw [genericToNormalization_normalizationToCover]
    unfold normalizedLift normalizationIsoCover
    simp only [asIso_inv, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [Pcf.schemeGenericToNormalization_comp]
    exact coverGenericInclusion_comp R S

variable [IsNoetherianRing R] [IsNoetherianRing S]

/-- The canonical lift of the cover to absolute normalizations is an isomorphism. -/
theorem canonicalLift_isIso :
    IsIso (Pcf.schemeGlobalNormalizationMorphism (schemeMap R S)) := by
  rw [← normalizedLift_eq_canonical R S]
  exact normalizedLift_isIso R S

/-- No divisor of the normalization has weighted degree above one. -/
theorem weightedCriticalPointSet_empty :
    haveI := normalizationMap_isFinite R S
    haveI := cover_normalizationMap_isFinite S
    Pcf.weightedCriticalPointSet (schemeMap R S) = ∅ := by
  haveI := normalizationMap_isFinite R S
  haveI := cover_normalizationMap_isFinite S
  letI : IsIso (Pcf.schemeGlobalNormalizationMorphism (schemeMap R S)) :=
    canonicalLift_isIso R S
  simp [Pcf.weightedCriticalPointSet, Pcf.schemeDivisorDelta_of_isIso]

/-- The normalized weighted branch locus of the birational cover is empty. -/
theorem weightedBranchLocus_empty :
    haveI := normalizationMap_isFinite R S
    haveI := cover_normalizationMap_isFinite S
    Pcf.weightedBranchLocus (schemeMap R S) = ∅ := by
  haveI := normalizationMap_isFinite R S
  haveI := cover_normalizationMap_isFinite S
  rw [Pcf.weightedBranchLocus_eq_image_criticalLocus]
  have h := weightedCriticalPointSet_empty R S
  simp [Pcf.weightedCriticalLocus, h]

end Pcf.Examples.PaperP.BirationalAffineNormalization

#print axioms Pcf.Examples.PaperP.BirationalAffineNormalization.normalizationToCover_isIso
#print axioms Pcf.Examples.PaperP.BirationalAffineNormalization.normalizationIsoCover_hom_comp
#print axioms Pcf.Examples.PaperP.BirationalAffineNormalization.normalizedLift_eq_canonical
#print axioms Pcf.Examples.PaperP.BirationalAffineNormalization.canonicalLift_isIso
#print axioms Pcf.Examples.PaperP.BirationalAffineNormalization.weightedBranchLocus_empty
