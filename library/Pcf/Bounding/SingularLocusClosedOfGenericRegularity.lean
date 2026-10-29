/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.NagataRegularLocus
public import Pcf.Bounding.PaperPBoundingSigmaClosedPerfectField

/-!
# Reduction of `07R5` over an arbitrary field to generic regularity

By Nagata's criterion (`isOpen_primeRegularLocus_of_forall_quotient`), the
singular locus of a scheme locally of finite type over a field `k` is closed
as soon as every finite-type `k`-domain is J-0, i.e. regular on a nonempty
basic open set (`FiniteTypeGenericRegularity k`). Over an imperfect field this
last statement is the remaining open input (Stacks Lemmas 15.48.4–15.48.6);
it is stated as an explicit hypothesis, not assumed.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/-- A ring is J-0 in the basic-open form: its regular locus contains `D(h)` for
some nonzero `h`. -/
def IsGenericallyRegular (A : Type u) [CommRing A] : Prop :=
  ∃ h : A, h ≠ 0 ∧ ∀ Q : PrimeSpectrum A, h ∉ Q.asIdeal → Q ∈ primeRegularLocus A

/-- Every finite-type domain over `k` is J-0 (generic regularity). -/
def FiniteTypeGenericRegularity (k : Type u) [Field k] : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A],
    IsGenericallyRegular A

/-- Generic regularity of finite-type domains gives openness of the regular
locus of every finite-type algebra. -/
theorem isOpen_primeRegularLocus_of_finiteTypeGenericRegularity
    {k : Type u} [Field k] (hk : FiniteTypeGenericRegularity k)
    (R : Type u) [CommRing R] [Algebra k R] [Algebra.FiniteType k R] :
    IsOpen (primeRegularLocus R) := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  refine isOpen_primeRegularLocus_of_forall_quotient R fun p hp ↦ ?_
  have : Algebra.FiniteType k (R ⧸ p) := .trans (S := R) inferInstance inferInstance
  obtain ⟨h, hh0, hh⟩ := hk (R ⧸ p)
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective h
  exact ⟨h, fun hm ↦ hh0 (Ideal.Quotient.eq_zero_iff_mem.mpr hm), hh⟩

set_option backward.isDefEq.respectTransparency false in
/-- Stacks Lemma 29.19.3 (1), closedness form, conditional on generic regularity
of finite-type domains over `k`. -/
theorem isClosed_stalkSingularLocus_of_finiteTypeGenericRegularity
    {k : Type u} [Field k] (hk : FiniteTypeGenericRegularity k) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    IsClosed (stalkSingularLocus X) := by
  rw [isClosed_stalkSingularLocus_iff_affine]
  intro V
  have hVU : (V : X.Opens) ≤ f ⁻¹ᵁ ⊤ := by simp
  let := (f.appLE ⊤ V hVU).hom.toAlgebra
  have hft : Algebra.FiniteType Γ(Spec (.of k), ⊤) Γ(X, V) :=
    f.finiteType_appLE (isAffineOpen_top _) V.2 hVU
  let eΓ : k ≃+* Γ(Spec (.of k), ⊤) :=
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv
  let : Algebra k Γ(Spec (.of k), ⊤) := eΓ.toRingHom.toAlgebra
  let : Algebra k Γ(X, V) :=
    ((algebraMap Γ(Spec (.of k), ⊤) Γ(X, V)).comp (algebraMap k Γ(Spec (.of k), ⊤))).toAlgebra
  have : IsScalarTower k Γ(Spec (.of k), ⊤) Γ(X, V) := .of_algebraMap_eq' rfl
  have : Algebra.FiniteType k Γ(Spec (.of k), ⊤) :=
    Algebra.FiniteType.of_surjective (Algebra.ofId k _) eΓ.surjective
  have : Algebra.FiniteType k Γ(X, V) := .trans this hft
  exact isOpen_primeRegularLocus_of_finiteTypeGenericRegularity hk Γ(X, V)

/-- `thm:bounding` Step 0 over an arbitrary field, conditional on generic
regularity of finite-type domains over `k`. -/
theorem paperPBoundingSigma_closed_proper_finite_of_finiteTypeGenericRegularity
    (k : Type u) [Field k] (hk : FiniteTypeGenericRegularity k)
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsNormalScheme Y] [NoetherianSpace X] [NoetherianSpace Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (hsep : IsGenericallySeparableSchemeMap f)
    (B : SchemeDivisorPoint Y) :
    IsClosed (paperPBoundingSigma f B) ∧
      paperPBoundingSigma f B ≠ Set.univ ∧
      {Q : SchemeDivisorPoint (pointClosureIdealSheaf B.1).subscheme |
        closure ({Q.1} : Set (pointClosureIdealSheaf B.1).subscheme) ⊆
          paperPBoundingSigma f B}.Finite :=
  paperPBoundingSigma_closed_proper_finite_of_singularClosed k s f hsep B
    (isClosed_stalkSingularLocus_of_finiteTypeGenericRegularity hk s)
    (isClosed_stalkSingularLocus_of_finiteTypeGenericRegularity hk
      ((pointClosureIdealSheaf B.1).subschemeι ≫ s))

/-- Bounding-data form of the previous theorem, for monodromy not divisible by
`p` (any `p : ℕ`, with `p = 0` the characteristic-zero case). -/
theorem paperPBoundingSigma_closed_proper_finite_of_primeToPMonodromy_of_genericRegularity
    (p : ℕ) (k : Type u) [Field k] (hk : FiniteTypeGenericRegularity k)
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X] [NoetherianSpace Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (hmono : IsPrimeToPMonodromyMap p f)
    (A : SchemeDivisorPoint X) :
    letI : IsFinite (Palomar.normalizationMap X) :=
      schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
    letI : IsFinite (Palomar.normalizationMap Y) :=
      schemeGlobalNormalizationMap_isFinite Y k s
    IsClosed (paperPBoundingSigma f (A.mapFiniteDominantNormal f)) ∧
      paperPBoundingSigma f (A.mapFiniteDominantNormal f) ≠ Set.univ ∧
      {Q : SchemeDivisorPoint
          (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme |
        closure ({Q.1} : Set
          (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme) ⊆
          paperPBoundingSigma f (A.mapFiniteDominantNormal f)}.Finite := by
  let : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
  let : IsFinite (Palomar.normalizationMap Y) :=
    schemeGlobalNormalizationMap_isFinite Y k s
  exact paperPBoundingSigma_closed_proper_finite_of_finiteTypeGenericRegularity k hk s f
    (isGenericallySeparableSchemeMap_of_primeToPMonodromyMap p f hmono)
    (A.mapFiniteDominantNormal f)

#print axioms isOpen_primeRegularLocus_of_finiteTypeGenericRegularity
#print axioms isClosed_stalkSingularLocus_of_finiteTypeGenericRegularity
#print axioms paperPBoundingSigma_closed_proper_finite_of_finiteTypeGenericRegularity
#print axioms paperPBoundingSigma_closed_proper_finite_of_primeToPMonodromy_of_genericRegularity

end Pcf
