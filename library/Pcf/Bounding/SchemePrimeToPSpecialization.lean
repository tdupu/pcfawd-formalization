/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PrimeToPRamification
public import Pcf.Stacks.Abhyankar.Tame.Defs
public import Pcf.Stacks.Abhyankar.Scheme.Defs
public import Pcf.Bounding.SchemeDynamics
public import Pcf.Bounding.SchemePrimeToPMonodromy
public import Pcf.Stacks.Abhyankar.Scheme.AffineTameLocal
public import Pcf.Bounding.TameLocalChart
public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.CharP.Algebra

/-!
# Prime-to-characteristic monodromy and tame divisorial specialization

The ramification and residue-field conclusions for a finite Galois closure
give the tame condition at every prime of its integral closure over a DVR.
This is the local algebra used in `latex/paper-p.tex`, Lemma
`lem:prime-to-p-restrict`, and the input required by the tame Abhyankar chart.
-/

@[expose] public section

universe u v w x y

namespace Pcf

open AlgebraicGeometry TopologicalSpace

set_option linter.style.haveILetI false

/-- On a nonempty affine target chart, the stalk at the image of the source
generic point is its actual fraction field.  This identifies the base field
in `IsPrimeToPMonodromyMap` with the field used by the affine cover. -/
theorem isFractionRing_targetGenericStalk_of_finiteDominant
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    (U : Y.affineOpens) [Nonempty (U : Y.Opens)] :
    let hmem : f (genericPoint X) ∈ (U : Y.Opens) := by
      rw [map_genericPoint_eq_of_isDominant f]
      exact ((genericPoint_spec Y).mem_open_set_iff U.1.isOpen).mpr
        (by simpa using ‹Nonempty (U : Y.Opens)›)
    letI : Algebra Γ(Y, U) (Y.presheaf.stalk (f (genericPoint X))) :=
      (Y.presheaf.germ U (f (genericPoint X)) hmem).hom.toAlgebra
    IsFractionRing Γ(Y, U) (Y.presheaf.stalk (f (genericPoint X))) := by
  let hmem : f (genericPoint X) ∈ (U : Y.Opens) := by
    rw [map_genericPoint_eq_of_isDominant f]
    exact ((genericPoint_spec Y).mem_open_set_iff U.1.isOpen).mpr
      (by simpa using ‹Nonempty (U : Y.Opens)›)
  letI : Algebra Γ(Y, U) (Y.presheaf.stalk (f (genericPoint X))) :=
    (Y.presheaf.germ U (f (genericPoint X)) hmem).hom.toAlgebra
  change IsFractionRing Γ(Y, U) (Y.presheaf.stalk (f (genericPoint X)))
  have hprime : U.2.primeIdealOf ⟨f (genericPoint X), hmem⟩ =
      genericPoint (Spec Γ(Y, U)) := by
    simpa only [map_genericPoint_eq_of_isDominant f] using
      (U.2.primeIdealOf_genericPoint)
  delta IsFractionRing IsLocalization.AtPrime
  convert (U.2.isLocalization_stalk ⟨f (genericPoint X), hmem⟩) using 1
  rw [hprime, genericPoint_eq_bot_of_affine]
  ext
  exact mem_nonZeroDivisors_iff_ne_zero

/-- The integral closure of a characteristic-`p` Dedekind domain in a finite
Galois extension of degree prime to `p` is tame at every prime.  The index is
a unit in the residue field, and the residue extension is separable.  This is
the Galois-closure step of `latex/paper-p.tex`, Lemma `lem:prime-to-p-restrict`.
-/
theorem galois_integralClosure_isTamelyRamifiedAt
    (p : ℕ) (hp : p.Prime)
    (R F L S : Type*) [CommRing R] [IsDedekindDomain R]
    [Field F] [Field L] [CommRing S]
    [CharP R p]
    [Algebra R F] [IsFractionRing R F]
    [Algebra F L] [IsGalois F L] [FiniteDimensional F L]
    [Algebra R S] [Algebra S L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R F L]
    [IsIntegralClosure S R L]
    (Q : PrimeSpectrum S)
    (hdegree : (Module.finrank F L).Coprime p) :
    Stacks.IsTamelyRamifiedAt R S Q := by
  let q := Q.asIdeal.under R
  letI : q.IsPrime := inferInstance
  letI : Q.asIdeal.LiesOver q := inferInstance
  letI : CharP q.ResidueField p :=
    CharP.of_ringHom_of_ne_zero (algebraMap R q.ResidueField) p hp.ne_zero
  letI : ExpChar q.ResidueField p := ExpChar.prime hp
  letI := Localization.AtPrime.algebraOfLiesOver q Q.asIdeal
  have h := galois_integralClosure_ramification_residue_coprime p hp R F L S
    q Q.asIdeal hdegree
  dsimp only [Stacks.IsTamelyRamifiedAt]
  refine ⟨?_, (isGalois_iff.mp h.2.1).1⟩
  exact (CharP.isUnit_natCast_iff hp).mpr
    (hp.coprime_iff_not_dvd.mp h.1.symm)

/-- Specialization descends from a Galois integral-closure model to a
compatible intermediate finite cover.  The tower law makes the intermediate
ramification index divide the Galois index, while its residue field embeds in
the Galois residue extension.  This is the final algebraic argument in
`latex/paper-p.tex`, Lemma `lem:prime-to-p-restrict`.

The flatness hypothesis is the local DVR flatness needed by Mathlib's tower
formula; at a divisor of a normal finite cover it follows from torsion
freeness over that DVR. -/
theorem primeToP_specialization_of_galois_integralClosure
    (p : ℕ) (hp : p.Prime)
    (R : Type u) (F : Type v) (N : Type w) (S : Type x) (T : Type y)
    [CommRing R] [IsDedekindDomain R] [CharP R p]
    [Field F] [Field N] [CommRing S] [CommRing T]
    [Algebra R F] [IsFractionRing R F]
    [Algebra F N] [IsGalois F N] [FiniteDimensional F N]
    [Algebra R T] [Algebra T N] [Algebra R N]
    [IsScalarTower R T N] [IsScalarTower R F N]
    [IsIntegralClosure T R N]
    [Algebra R S] [Algebra S T] [IsScalarTower R S T]
    [Module.Flat S T]
    (P : Ideal S) [P.IsPrime] (Q : Ideal T) [Q.IsPrime] [Q.LiesOver P]
    (hdegree : (Module.finrank F N).Coprime p) :
    (P.ramificationIdx R).Coprime p ∧
      (letI := Localization.AtPrime.algebraOfLiesOver (P.under R) P
       IsPrimeToPMonodromy.{u, x, y} p (P.under R).ResidueField P.ResidueField) := by
  let q := P.under R
  letI : q.IsPrime := inferInstance
  letI : P.LiesOver q := inferInstance
  letI : Q.LiesOver q := inferInstance
  letI : CharP q.ResidueField p :=
    CharP.of_ringHom_of_ne_zero (algebraMap R q.ResidueField) p hp.ne_zero
  letI : ExpChar q.ResidueField p := ExpChar.prime hp
  letI := Localization.AtPrime.algebraOfLiesOver q P
  letI := Localization.AtPrime.algebraOfLiesOver q Q
  letI := Localization.AtPrime.algebraOfLiesOver P Q
  have hG := galois_integralClosure_ramification_residue_coprime p hp R F N T
    q Q hdegree
  have htower : Q.ramificationIdx R = P.ramificationIdx R * Q.ramificationIdx S :=
    Ideal.ramificationIdx_tower (R := R) P Q
  have hdiv : P.ramificationIdx R ∣ Q.ramificationIdx R := by
    rw [htower]
    exact dvd_mul_right _ _
  constructor
  · exact Nat.Coprime.of_dvd_left hdiv hG.1
  · letI : IsGalois q.ResidueField Q.ResidueField := hG.2.1
    letI : FiniteDimensional q.ResidueField Q.ResidueField :=
      Module.finite_of_finrank_pos (by
        apply Nat.pos_of_ne_zero
        intro hz
        exact (hp.coprime_iff_not_dvd.mp hG.2.2.symm) (hz ▸ dvd_zero p))
    exact isPrimeToPMonodromy_of_embedding_into_galois p q.ResidueField
      P.ResidueField Q.ResidueField
      (IsScalarTower.toAlgHom q.ResidueField P.ResidueField Q.ResidueField) hG.2.2

/-- The intermediate prime in the preceding tower satisfies exactly the
pointwise tame predicate consumed by the Abhyankar chart (Stacks Tag `09E9`). -/
theorem primeToP_specialization_isTamelyRamifiedAt
    (p : ℕ) (hp : p.Prime)
    (R : Type u) (F : Type v) (N : Type w) (S : Type x) (T : Type y)
    [CommRing R] [IsDedekindDomain R] [CharP R p]
    [Field F] [Field N] [CommRing S] [CommRing T]
    [Algebra R F] [IsFractionRing R F]
    [Algebra F N] [IsGalois F N] [FiniteDimensional F N]
    [Algebra R T] [Algebra T N] [Algebra R N]
    [IsScalarTower R T N] [IsScalarTower R F N]
    [IsIntegralClosure T R N]
    [Algebra R S] [Algebra S T] [IsScalarTower R S T]
    [Module.Flat S T]
    (P : Ideal S) [P.IsPrime] (Q : Ideal T) [Q.IsPrime] [Q.LiesOver P]
    (hdegree : (Module.finrank F N).Coprime p) :
    Stacks.IsTamelyRamifiedAt R S ⟨P, ‹P.IsPrime›⟩ := by
  let q := P.under R
  letI : q.IsPrime := inferInstance
  letI := Localization.AtPrime.algebraOfLiesOver q P
  obtain ⟨hidx, ⟨C⟩⟩ :=
    primeToP_specialization_of_galois_integralClosure p hp R F N S T P Q hdegree
  letI : CharP q.ResidueField p :=
    CharP.of_ringHom_of_ne_zero (algebraMap R q.ResidueField) p hp.ne_zero
  change IsUnit ((P.ramificationIdx R : ℕ) : q.ResidueField) ∧
    Algebra.IsSeparable q.ResidueField P.ResidueField
  exact ⟨(CharP.isUnit_natCast_iff hp).mpr (hp.coprime_iff_not_dvd.mp hidx.symm),
    C.separable⟩

/-- A finite intermediate cover of the Galois integral-closure model is tame
in codimension one along every principal divisor.  Integrality and faithful
embedding provide a prime of the Galois closure above each intermediate
prime; the preceding theorem handles that prime. -/
theorem primeToP_specialization_isTamelyRamifiedInCodimensionOneAlong
    (p : ℕ) (hp : p.Prime)
    (R : Type u) (F : Type v) (N : Type w) (S : Type x) (T : Type y)
    [CommRing R] [IsDedekindDomain R] [CharP R p]
    [Field F] [Field N] [CommRing S] [CommRing T]
    [Algebra R F] [IsFractionRing R F]
    [Algebra F N] [IsGalois F N] [FiniteDimensional F N]
    [Algebra R T] [Algebra T N] [Algebra R N]
    [IsScalarTower R T N] [IsScalarTower R F N]
    [IsIntegralClosure T R N]
    [Algebra R S] [Algebra S T] [IsScalarTower R S T]
    [Module.Flat S T] [FaithfulSMul S T]
    (a : R) (hdegree : (Module.finrank F N).Coprime p) :
    Stacks.IsTamelyRamifiedInCodimensionOneAlong R S a := by
  letI : Algebra.IsIntegral R T := IsIntegralClosure.isIntegral_algebra R N
  letI : Algebra.IsIntegral S T := Algebra.IsIntegral.tower_top R
  intro P _ _
  obtain ⟨Q⟩ : Nonempty (P.asIdeal.primesOver T) := inferInstance
  letI : Q.1.IsPrime := Q.2.1
  letI : Q.1.LiesOver P.asIdeal := Q.2.2
  exact primeToP_specialization_isTamelyRamifiedAt p hp R F N S T P.asIdeal Q.1 hdegree

/-- A finite normal cover of a characteristic-`p` Dedekind domain is tame in
codimension one when its function-field extension has prime-to-`p` monodromy.
The Galois closure certificate constructs the finite integral-closure tower;
the cover itself embeds in that tower because it is integral over the base.
This is the affine DVR form of `latex/paper-p.tex`, Lemma
`lem:prime-to-p-restrict`. -/
theorem finiteNormalCover_isTamelyRamifiedInCodimensionOneAlong
    (p : ℕ) (hp : p.Prime)
    (R S : Type u) (F E : Type u)
    [CommRing R] [IsDedekindDomain R] [CharP R p]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
    [Field F] [Field E]
    [Algebra R F] [IsFractionRing R F]
    [Algebra S E] [IsFractionRing S E]
    [Algebra R E] [IsScalarTower R S E]
    [Algebra F E] [IsScalarTower R F E]
    (hmono : IsPrimeToPMonodromy.{u, u, u} p F E)
    (a : R) : Stacks.IsTamelyRamifiedInCodimensionOneAlong R S a := by
  obtain ⟨C⟩ := hmono
  letI := C.field
  letI := C.algebra
  letI := C.finiteClosure
  letI : IsGalois F C.Closure := C.isGaloisClosure
  letI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  letI : IsIntegralClosure S R E := IsIntegralClosure.of_isIntegrallyClosed S R E
  letI : FiniteDimensional F E := C.finite_extension
  letI : Algebra.IsSeparable F E := C.separable
  letI : IsDedekindDomain S := IsIntegralClosure.isDedekindDomain R F E S
  letI : Algebra R C.Closure :=
    ((algebraMap F C.Closure).comp (algebraMap R F)).toAlgebra
  letI : IsScalarTower R F C.Closure := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra S C.Closure :=
    (C.embedding.toRingHom.comp (algebraMap S E)).toAlgebra
  letI : IsScalarTower R S C.Closure := IsScalarTower.of_algebraMap_eq' (by
    ext r
    change algebraMap F C.Closure (algebraMap R F r) =
      C.embedding (algebraMap S E (algebraMap R S r))
    rw [← IsScalarTower.algebraMap_apply R S E]
    calc
      algebraMap F C.Closure (algebraMap R F r) =
          C.embedding (algebraMap F E (algebraMap R F r)) :=
        (C.embedding.commutes _).symm
      _ = C.embedding (algebraMap R E r) := by
        rw [IsScalarTower.algebraMap_apply R F E])
  let T := integralClosure R C.Closure
  let ι : S →ₐ[R] T := IsIntegralClosure.lift R T C.Closure
  letI : Algebra S T := ι.toRingHom.toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' (by
    ext r
    apply congrArg (fun t : T => (t : C.Closure))
    exact (ι.commutes r).symm)
  letI : FaithfulSMul S T := (faithfulSMul_iff_algebraMap_injective S T).mpr (by
    intro s t h
    have h' := congrArg (algebraMap T C.Closure) h
    change algebraMap T C.Closure (ι s) = algebraMap T C.Closure (ι t) at h'
    rw [IsIntegralClosure.algebraMap_lift, IsIntegralClosure.algebraMap_lift] at h'
    exact (IsFractionRing.injective S E) (C.embedding.injective h'))
  letI : Module.IsTorsionFree S T := Module.IsTorsionFree.of_smul_eq_zero (by
    intro s t ht
    by_cases hs : s = 0
    · exact Or.inl hs
    · right
      have hs' : algebraMap S T s ≠ 0 :=
        by simpa only [map_zero] using (FaithfulSMul.algebraMap_injective S T).ne hs
      exact (mul_eq_zero.mp (show algebraMap S T s * t = 0 by simpa [Algebra.smul_def] using ht))
        |>.resolve_left hs')
  letI : Module.Flat S T := inferInstance
  exact primeToP_specialization_isTamelyRamifiedInCodimensionOneAlong
    p hp R F C.Closure S T a C.coprimeDegree

/-- On a Dedekind affine target chart, the monodromy certificate of the actual
finite scheme morphism gives the affine tame predicate on its full finite
preimage.  In particular, the fraction fields and their inclusion are the
ones induced by the generic stalk map and the two section-to-stalk maps. -/
theorem finiteNormalAffinePreimage_isTamelyRamifiedInCodimensionOneAlong
    (p : ℕ) (hp : p.Prime)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X]
    (U : Y.affineOpens) [Nonempty (U : Y.Opens)]
    [IsDedekindDomain Γ(Y, U)] [CharP Γ(Y, U) p]
    (hmono : IsPrimeToPMonodromyMap p f) (a : Γ(Y, U)) :
    letI : Algebra Γ(Y, U) Γ(X, finitePreimageAffine f U) :=
      (f.app U).hom.toAlgebra
    Stacks.IsTamelyRamifiedInCodimensionOneAlong
      Γ(Y, U) Γ(X, finitePreimageAffine f U) a := by
  let V := finitePreimageAffine f U
  have hgp : f (genericPoint X) = genericPoint Y :=
    map_genericPoint_eq_of_isDominant f
  have hmem : f (genericPoint X) ∈ (U : Y.Opens) := by
    rw [hgp]
    exact ((genericPoint_spec Y).mem_open_set_iff U.1.isOpen).mpr
      (by simpa using ‹Nonempty (U : Y.Opens)›)
  letI : Nonempty (V : X.Opens) := ⟨⟨genericPoint X, hmem⟩⟩
  let R := Γ(Y, U)
  let S := Γ(X, V)
  let F := Y.presheaf.stalk (f (genericPoint X))
  let E := X.functionField
  letI : Algebra R S := (f.app U).hom.toAlgebra
  letI : Module.Finite R S := moduleFinite_finitePreimageAffine f U
  letI : FaithfulSMul R S := faithfulSMul_finitePreimageAffine f U
  letI : IsIntegrallyClosed S := IsNormalScheme.component_integrallyClosed V
  let e := (Y.presheaf.stalkCongr (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  have hfield : IsField F := e.toMulEquiv.isField (Field.toIsField _)
  letI : Field F := hfield.toField
  letI : Algebra R F :=
    (Y.presheaf.germ U (f (genericPoint X)) hmem).hom.toAlgebra
  letI : IsFractionRing R F :=
    isFractionRing_targetGenericStalk_of_finiteDominant f U
  letI : IsFractionRing S E :=
    functionField_isFractionRing_of_isAffineOpen X V V.2
  letI : Algebra R E :=
    ((X.germToFunctionField V).hom.comp (f.app U).hom).toAlgebra
  letI : IsScalarTower R S E := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra F E := (f.stalkMap (genericPoint X)).hom.toAlgebra
  letI : IsScalarTower R F E := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact (f.germ_stalkMap_apply U (genericPoint X) hmem r).symm)
  exact finiteNormalCover_isTamelyRamifiedInCodimensionOneAlong
    p hp R S F E hmono a

/-- A finite normal cover with prime-to-characteristic function-field
monodromy is tame at every prime over a height-one prime of a normal
Noetherian base.  Localizing at that base prime gives a DVR and a finite
normal cover with the same fraction-field extension; the tame conclusion
then descends to the original prime.  This is the codimension-one
specialization of `latex/paper-p.tex`, Lemma `lem:prime-to-p-restrict`. -/
theorem finiteNormalCover_isTamelyRamifiedAt_of_heightOne
    (pchar : ℕ) (hpchar : pchar.Prime)
    (R S F E : Type u)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
    [Field F] [Field E]
    [Algebra R F] [IsFractionRing R F]
    [Algebra S E] [IsFractionRing S E]
    [Algebra R E] [IsScalarTower R S E]
    [Algebra F E] [IsScalarTower R F E]
    [CharP R pchar]
    (hmono : IsPrimeToPMonodromy.{u, u, u} pchar F E)
    (P : Ideal R) [P.IsPrime] (hP : P.height = 1)
    (Q : PrimeSpectrum S) (hQ : Q.asIdeal.under R = P) :
    Stacks.IsTamelyRamifiedAt R S Q := by
  let Rp := Localization.AtPrime P
  let Sp := Localization (Algebra.algebraMapSubmonoid S P.primeCompl)
  letI : IsDiscreteValuationRing Rp :=
    isDiscreteValuationRing_localizationAtPrime_of_heightOne P hP
  letI : IsDedekindDomain Rp := inferInstance
  letI : CharP Rp pchar :=
    CharP.of_ringHom_of_ne_zero (algebraMap R Rp) pchar hpchar.ne_zero
  letI : FaithfulSMul Rp Sp := faithfulSMul_localization_algebraMapSubmonoid P
  letI : IsIntegrallyClosed Sp := isIntegrallyClosed_localization_algebraMapSubmonoid P
  letI : Module.Finite Rp Sp := inferInstance
  letI : Algebra Rp F :=
    IsLocalization.localizationAlgebraOfSubmonoidLe Rp F
      P.primeCompl (nonZeroDivisors R) P.primeCompl_le_nonZeroDivisors
  letI : IsScalarTower R Rp F :=
    IsLocalization.localization_isScalarTower_of_submonoid_le Rp F
      P.primeCompl (nonZeroDivisors R) P.primeCompl_le_nonZeroDivisors
  letI : IsFractionRing Rp F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl Rp F
  have hM : Algebra.algebraMapSubmonoid S P.primeCompl ≤ nonZeroDivisors S :=
    map_le_nonZeroDivisors_of_injective _
      (FaithfulSMul.algebraMap_injective R S) P.primeCompl_le_nonZeroDivisors
  letI : Algebra Sp E :=
    IsLocalization.localizationAlgebraOfSubmonoidLe Sp E
      (Algebra.algebraMapSubmonoid S P.primeCompl) (nonZeroDivisors S) hM
  letI : IsScalarTower S Sp E :=
    IsLocalization.localization_isScalarTower_of_submonoid_le Sp E
      (Algebra.algebraMapSubmonoid S P.primeCompl) (nonZeroDivisors S) hM
  letI : IsFractionRing Sp E :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Algebra.algebraMapSubmonoid S P.primeCompl) Sp E
  letI : Algebra Rp E := ((algebraMap F E).comp (algebraMap Rp F)).toAlgebra
  letI : IsScalarTower Rp F E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Rp Sp E := IsScalarTower.of_algebraMap_eq' (by
    apply IsLocalization.ringHom_ext P.primeCompl
    ext r
    calc
      algebraMap Rp E (algebraMap R Rp r) =
          algebraMap F E (algebraMap Rp F (algebraMap R Rp r)) := rfl
      _ = algebraMap F E (algebraMap R F r) := by
        rw [IsScalarTower.algebraMap_apply R Rp F]
      _ = algebraMap R E r := by
        rw [IsScalarTower.algebraMap_apply R F E]
      _ = algebraMap S E (algebraMap R S r) := by
        rw [IsScalarTower.algebraMap_apply R S E]
      _ = algebraMap Sp E (algebraMap Rp Sp (algebraMap R Rp r)) := by
        calc
          algebraMap S E (algebraMap R S r) =
              algebraMap Sp E (algebraMap S Sp (algebraMap R S r)) :=
            (IsScalarTower.algebraMap_apply S Sp E _)
          _ = algebraMap Sp E (algebraMap R Sp r) :=
            congrArg (algebraMap Sp E) (IsScalarTower.algebraMap_apply R S Sp r)
          _ = algebraMap Sp E (algebraMap Rp Sp (algebraMap R Rp r)) :=
            congrArg (algebraMap Sp E) (IsScalarTower.algebraMap_apply R Rp Sp r))
  have hPne : P ≠ ⊥ := by
    intro h
    have h0 : P.height = 0 := Ideal.height_eq_zero_iff_eq_bot.mpr h
    rw [hP] at h0
    norm_num at h0
  obtain ⟨b, hbP, hb0⟩ := P.ne_bot_iff.mp hPne
  let a : Rp := algebraMap R Rp b
  have ha0 : a ≠ 0 := by
    simpa only [map_zero] using
      (IsLocalization.injective Rp P.primeCompl_le_nonZeroDivisors).ne hb0
  have ha : a ∈ nonZeroDivisors Rp := mem_nonZeroDivisors_iff_ne_zero.mpr ha0
  have haSp0 : algebraMap Rp Sp a ≠ 0 := by
    simpa only [map_zero] using (FaithfulSMul.algebraMap_injective Rp Sp).ne ha0
  have haSp : algebraMap Rp Sp a ∈ nonZeroDivisors Sp :=
    mem_nonZeroDivisors_iff_ne_zero.mpr haSp0
  have htame : Stacks.IsTamelyRamifiedInCodimensionOneAlong Rp Sp a :=
    finiteNormalCover_isTamelyRamifiedInCodimensionOneAlong
      pchar hpchar Rp Sp F E hmono a
  letI : Q.asIdeal.LiesOver P := ⟨hQ.symm⟩
  let Q' : PrimeSpectrum Sp := ⟨Q.asIdeal.map (algebraMap S Sp),
    Stacks.SchemeLevel.AffineTame.isPrime_map_localizationAtPrime P Sp Q.asIdeal hQ⟩
  have hQlocal : Q'.asIdeal.LiesOver (IsLocalRing.maximalIdeal Rp) :=
    IsLocalization.AtPrime.liesOver_map_of_liesOver P Rp Sp Q.asIdeal
  have hmaxheight : (IsLocalRing.maximalIdeal Rp).height = 1 :=
    WithBot.coe_eq_coe.mp
      (IsLocalRing.maximalIdeal_height_eq_ringKrullDim.trans
        (IsDiscreteValuationRing.ringKrullDim_eq_one Rp))
  have haMax : a ∈ IsLocalRing.maximalIdeal Rp :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff Rp P b).mpr hbP
  have hpoint : Stacks.IsTamelyRamifiedAt Rp Sp Q' :=
    ((Stacks.isTamelyRamifiedInCodimensionOneAlong_iff ha haSp).mp htame)
      Q' (by rw [← hQlocal.over]; exact hmaxheight)
      (by rw [← hQlocal.over]; exact haMax)
  exact Stacks.SchemeLevel.AffineTame.isTamelyRamifiedAt_of_isLocalization
    P Rp Sp Q hQ hpoint


/-- Prime-to-`p` monodromy makes a finite normal cover of a normal
Noetherian base tame in codimension one along any effective principal
divisor.  This is the full affine tameness statement needed by the
two-dimensional local Abhyankar chart. -/
theorem finiteNormalCover_isTamelyRamifiedInCodimensionOneAlong_of_noetherian
    (pchar : ℕ) (hpchar : pchar.Prime)
    (R S F E : Type u)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
    [Field F] [Field E]
    [Algebra R F] [IsFractionRing R F]
    [Algebra S E] [IsFractionRing S E]
    [Algebra R E] [IsScalarTower R S E]
    [Algebra F E] [IsScalarTower R F E]
    [CharP R pchar]
    (hmono : IsPrimeToPMonodromy.{u, u, u} pchar F E)
    (a : R) (ha : a ∈ nonZeroDivisors R) :
    Stacks.IsTamelyRamifiedInCodimensionOneAlong R S a := by
  have haS0 : algebraMap R S a ≠ 0 := by
    have ha0 : a ≠ 0 := (mem_nonZeroDivisors_iff_ne_zero.mp ha)
    simpa only [map_zero] using (FaithfulSMul.algebraMap_injective R S).ne ha0
  have haS : algebraMap R S a ∈ nonZeroDivisors S :=
    mem_nonZeroDivisors_iff_ne_zero.mpr haS0
  apply (Stacks.isTamelyRamifiedInCodimensionOneAlong_iff ha haS).mpr
  intro Q hheight _
  exact finiteNormalCover_isTamelyRamifiedAt_of_heightOne
    pchar hpchar R S F E hmono (Q.asIdeal.under R) hheight Q rfl

/-- Simultaneously localizing the base and finite normal cover preserves the
prime-to-`p` function-field certificate and gives precisely the tame
predicate required by a two-dimensional local Abhyankar chart. -/
theorem finiteNormalCover_localization_isTamelyRamifiedInCodimensionOneAlong
    (pchar : ℕ) (hpchar : pchar.Prime)
    (R S F E : Type u)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
    [Field F] [Field E]
    [Algebra R F] [IsFractionRing R F]
    [Algebra S E] [IsFractionRing S E]
    [Algebra R E] [IsScalarTower R S E]
    [Algebra F E] [IsScalarTower R F E]
    [CharP R pchar]
    (hmono : IsPrimeToPMonodromy.{u, u, u} pchar F E)
    (q : Ideal R) [q.IsPrime]
    (a : Localization.AtPrime q) (ha : a ∈ nonZeroDivisors (Localization.AtPrime q)) :
    Stacks.IsTamelyRamifiedInCodimensionOneAlong
      (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)) a := by
  let Rp := Localization.AtPrime q
  let Sp := Localization (Algebra.algebraMapSubmonoid S q.primeCompl)
  letI : IsIntegrallyClosed Rp :=
    isIntegrallyClosed_of_isLocalization _ _ q.primeCompl_le_nonZeroDivisors
  letI : CharP Rp pchar :=
    CharP.of_ringHom_of_ne_zero (algebraMap R Rp) pchar hpchar.ne_zero
  letI : FaithfulSMul Rp Sp := faithfulSMul_localization_algebraMapSubmonoid q
  letI : IsIntegrallyClosed Sp := isIntegrallyClosed_localization_algebraMapSubmonoid q
  letI : Module.Finite Rp Sp := inferInstance
  letI : Algebra Rp F :=
    IsLocalization.localizationAlgebraOfSubmonoidLe Rp F
      q.primeCompl (nonZeroDivisors R) q.primeCompl_le_nonZeroDivisors
  letI : IsScalarTower R Rp F :=
    IsLocalization.localization_isScalarTower_of_submonoid_le Rp F
      q.primeCompl (nonZeroDivisors R) q.primeCompl_le_nonZeroDivisors
  letI : IsFractionRing Rp F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl Rp F
  have hM : Algebra.algebraMapSubmonoid S q.primeCompl ≤ nonZeroDivisors S :=
    map_le_nonZeroDivisors_of_injective _
      (FaithfulSMul.algebraMap_injective R S) q.primeCompl_le_nonZeroDivisors
  letI : Algebra Sp E :=
    IsLocalization.localizationAlgebraOfSubmonoidLe Sp E
      (Algebra.algebraMapSubmonoid S q.primeCompl) (nonZeroDivisors S) hM
  letI : IsScalarTower S Sp E :=
    IsLocalization.localization_isScalarTower_of_submonoid_le Sp E
      (Algebra.algebraMapSubmonoid S q.primeCompl) (nonZeroDivisors S) hM
  letI : IsFractionRing Sp E :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Algebra.algebraMapSubmonoid S q.primeCompl) Sp E
  letI : Algebra Rp E := ((algebraMap F E).comp (algebraMap Rp F)).toAlgebra
  letI : IsScalarTower Rp F E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Rp Sp E := IsScalarTower.of_algebraMap_eq' (by
    apply IsLocalization.ringHom_ext q.primeCompl
    ext r
    calc
      algebraMap Rp E (algebraMap R Rp r) =
          algebraMap F E (algebraMap Rp F (algebraMap R Rp r)) := rfl
      _ = algebraMap F E (algebraMap R F r) := by
        rw [IsScalarTower.algebraMap_apply R Rp F]
      _ = algebraMap R E r := by
        rw [IsScalarTower.algebraMap_apply R F E]
      _ = algebraMap S E (algebraMap R S r) := by
        rw [IsScalarTower.algebraMap_apply R S E]
      _ = algebraMap Sp E (algebraMap Rp Sp (algebraMap R Rp r)) := by
        calc
          algebraMap S E (algebraMap R S r) =
              algebraMap Sp E (algebraMap S Sp (algebraMap R S r)) :=
            IsScalarTower.algebraMap_apply S Sp E _
          _ = algebraMap Sp E (algebraMap R Sp r) :=
            congrArg (algebraMap Sp E) (IsScalarTower.algebraMap_apply R S Sp r)
          _ = algebraMap Sp E (algebraMap Rp Sp (algebraMap R Rp r)) :=
            congrArg (algebraMap Sp E) (IsScalarTower.algebraMap_apply R Rp Sp r))
  exact finiteNormalCover_isTamelyRamifiedInCodimensionOneAlong_of_noetherian
    pchar hpchar Rp Sp F E hmono a ha

/-- For an actual finite dominant map of normal integral schemes, prime-to-`p`
monodromy supplies the tame predicate after localizing any finite affine
preimage at a base prime.  With a nonzero local divisor equation this has
exactly the type of `TameLocalBoundingChart.ofFiniteNormalLocalization`'s
`tame` argument, including at codimension-two points. -/
theorem finiteNormalAffinePreimage_localization_isTamelyRamifiedInCodimensionOneAlong
    (pchar : ℕ) (hpchar : pchar.Prime)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y] [IsLocallyNoetherian Y]
    (U : Y.affineOpens) [Nonempty (U : Y.Opens)]
    [CharP Γ(Y, U) pchar]
    (hmono : IsPrimeToPMonodromyMap pchar f)
    (q : Ideal Γ(Y, U)) [q.IsPrime]
    (a : Localization.AtPrime q)
    (ha : a ∈ nonZeroDivisors (Localization.AtPrime q)) :
    letI : Algebra Γ(Y, U) Γ(X, finitePreimageAffine f U) :=
      (f.app U).hom.toAlgebra
    Stacks.IsTamelyRamifiedInCodimensionOneAlong
      (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U) q.primeCompl)) a := by
  let V := finitePreimageAffine f U
  have hgp : f (genericPoint X) = genericPoint Y :=
    map_genericPoint_eq_of_isDominant f
  have hmem : f (genericPoint X) ∈ (U : Y.Opens) := by
    rw [hgp]
    exact ((genericPoint_spec Y).mem_open_set_iff U.1.isOpen).mpr
      (by simpa using ‹Nonempty (U : Y.Opens)›)
  letI : Nonempty (V : X.Opens) := ⟨⟨genericPoint X, hmem⟩⟩
  let R := Γ(Y, U)
  let S := Γ(X, V)
  let F := Y.presheaf.stalk (f (genericPoint X))
  let E := X.functionField
  letI : Algebra R S := (f.app U).hom.toAlgebra
  letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian U
  letI : IsIntegrallyClosed R := IsNormalScheme.component_integrallyClosed U
  letI : IsIntegrallyClosed S := IsNormalScheme.component_integrallyClosed V
  letI : Module.Finite R S := moduleFinite_finitePreimageAffine f U
  letI : FaithfulSMul R S := faithfulSMul_finitePreimageAffine f U
  let e := (Y.presheaf.stalkCongr (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  have hfield : IsField F := e.toMulEquiv.isField (Field.toIsField _)
  letI : Field F := hfield.toField
  letI : Algebra R F :=
    (Y.presheaf.germ U (f (genericPoint X)) hmem).hom.toAlgebra
  letI : IsFractionRing R F :=
    isFractionRing_targetGenericStalk_of_finiteDominant f U
  letI : IsFractionRing S E :=
    functionField_isFractionRing_of_isAffineOpen X V V.2
  letI : Algebra R E :=
    ((X.germToFunctionField V).hom.comp (f.app U).hom).toAlgebra
  letI : IsScalarTower R S E := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra F E := (f.stalkMap (genericPoint X)).hom.toAlgebra
  letI : IsScalarTower R F E := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact (f.germ_stalkMap_apply U (genericPoint X) hmem r).symm)
  exact finiteNormalCover_localization_isTamelyRamifiedInCodimensionOneAlong
    pchar hpchar R S F E hmono q a ha

/-- The prime-to-`p` certificate of the actual scheme map supplies the tame
field of the local bounding chart.  The remaining arguments are precisely
the geometric regularity, generic étaleness, and branch-locus data of the
chart; finiteness, normality, faithfulness, and tameness are constructed. -/
theorem tameLocalBoundingChart_ofFiniteNormalAffinePreimage
    (pchar : ℕ) (hpchar : pchar.Prime)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y] [IsLocallyNoetherian Y]
    (U : Y.affineOpens) [Nonempty (U : Y.Opens)]
    [CharP Γ(Y, U) pchar]
    (hmono : IsPrimeToPMonodromyMap pchar f) :
    letI : Algebra Γ(Y, U) Γ(X, finitePreimageAffine f U) :=
      (f.app U).hom.toAlgebra
    ∀ (q : Ideal Γ(Y, U)) [q.IsPrime]
    (a : Localization.AtPrime q)
    (p : Ideal (Localization (Algebra.algebraMapSubmonoid
      Γ(X, finitePreimageAffine f U) q.primeCompl))) [p.IsPrime]
    (_regular_base : IsRegularLocalRing (Localization.AtPrime q))
    (_dim_base : ringKrullDim (Localization.AtPrime q) = 2)
    (_regular_divisor : IsRegularLocalRing
      (Localization.AtPrime q ⧸ Ideal.span {a}))
    (_dim_divisor : ringKrullDim
      (Localization.AtPrime q ⧸ Ideal.span {a}) = 1)
    (_generic_etale : ∀ w : PrimeSpectrum
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U) q.primeCompl)),
      w.asIdeal.height = 0 → Algebra.IsEtaleAt (Localization.AtPrime q) w.asIdeal)
    (_unramified_codim_one : ∀ w : PrimeSpectrum
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U) q.primeCompl)),
      w.asIdeal.height = 1 →
        algebraMap (Localization.AtPrime q)
          (Localization (Algebra.algebraMapSubmonoid
            Γ(X, finitePreimageAffine f U) q.primeCompl)) a ∉ w.asIdeal →
        Algebra.IsUnramifiedAt (Localization.AtPrime q) w.asIdeal)
    (_height_cover_divisor : p.height = 1)
    (_equation_mem : algebraMap (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U) q.primeCompl)) a ∈ p),
    TameLocalBoundingChart (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U) q.primeCompl)) a p := by
  letI : Algebra Γ(Y, U) Γ(X, finitePreimageAffine f U) :=
    (f.app U).hom.toAlgebra
  intro q _ a p _ regular_base dim_base regular_divisor dim_divisor
    generic_etale unramified_codim_one height_cover_divisor equation_mem
  let V := finitePreimageAffine f U
  have hgp : f (genericPoint X) = genericPoint Y :=
    map_genericPoint_eq_of_isDominant f
  have hmem : f (genericPoint X) ∈ (U : Y.Opens) := by
    rw [hgp]
    exact ((genericPoint_spec Y).mem_open_set_iff U.1.isOpen).mpr
      (by simpa using ‹Nonempty (U : Y.Opens)›)
  letI : Nonempty (V : X.Opens) := ⟨⟨genericPoint X, hmem⟩⟩
  let R := Γ(Y, U)
  let S := Γ(X, V)
  letI : Algebra R S := (f.app U).hom.toAlgebra
  letI : Module.Finite R S := moduleFinite_finitePreimageAffine f U
  letI : FaithfulSMul R S := faithfulSMul_finitePreimageAffine f U
  letI : IsIntegrallyClosed R := IsNormalScheme.component_integrallyClosed U
  letI : IsIntegrallyClosed S := IsNormalScheme.component_integrallyClosed V
  have ha : a ∈ nonZeroDivisors (Localization.AtPrime q) :=
    mem_nonZeroDivisors_of_ringKrullDim_eq_two_of_quotient_eq_one
      dim_base dim_divisor
  let hAlg : Algebra R S := (f.app U).hom.toAlgebra
  exact @TameLocalBoundingChart.ofFiniteNormalLocalization R S
    (inferInstance) (inferInstance) hAlg
    (moduleFinite_finitePreimageAffine f U)
    (faithfulSMul_finitePreimageAffine f U)
    (inferInstance) (inferInstance)
    (inferInstance) (inferInstance) q (inferInstance) a p (inferInstance)
    regular_base dim_base regular_divisor dim_divisor
    generic_etale unramified_codim_one height_cover_divisor equation_mem
    (finiteNormalAffinePreimage_localization_isTamelyRamifiedInCodimensionOneAlong
      pchar hpchar f U hmono q a ha)

/-- Every codimension-one specialization along a principal divisor is tame
for the finite Galois integral-closure model.  The conclusion is precisely
the affine predicate used in the tame Abhyankar lemma. -/
theorem galois_integralClosure_isTamelyRamifiedInCodimensionOneAlong
    (p : ℕ) (hp : p.Prime)
    (R F L S : Type*) [CommRing R] [IsDedekindDomain R]
    [Field F] [Field L] [CommRing S]
    [CharP R p]
    [Algebra R F] [IsFractionRing R F]
    [Algebra F L] [IsGalois F L] [FiniteDimensional F L]
    [Algebra R S] [Algebra S L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R F L]
    [IsIntegralClosure S R L]
    (a : R) (hdegree : (Module.finrank F L).Coprime p) :
    Stacks.IsTamelyRamifiedInCodimensionOneAlong R S a := by
  intro Q _ _
  exact galois_integralClosure_isTamelyRamifiedAt p hp R F L S Q hdegree

/-- In a characteristic-`p` DVR, a prime-to-`p` finite Galois extension of
the fraction field is tamely ramified in the intrinsic sense of Stacks
Definition 15.113.7 (Tag `09E9`). -/
theorem galois_isTamelyRamifiedOver
    (p : ℕ) (hp : p.Prime)
    (R F L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CharP R p] [Field F] [Field L]
    [Algebra R F] [IsFractionRing R F]
    [Algebra F L] [IsGalois F L] [FiniteDimensional F L]
    [Algebra R L] [IsScalarTower R F L]
    (hdegree : (Module.finrank F L).Coprime p) :
    Stacks.SchemeLevel.IsTamelyRamifiedOver R L := by
  intro m hm
  exact galois_integralClosure_isTamelyRamifiedAt p hp R F L
    (integralClosure R L) ⟨m, hm.isPrime⟩ hdegree

/-- The Galois closure is tame over the actual local ring at a codimension-one
point of a normal locally Noetherian integral scheme.  Normality makes that
stalk a DVR; the arithmetic conclusion is the local Galois calculation above.
This is the geometric base-DVR step in `latex/paper-p.tex`, Lemma
`lem:prime-to-p-restrict`. -/
theorem galois_schemeDivisorStalk_isTamelyRamifiedOver
    (p : ℕ) (hp : p.Prime) {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
    [IsNormalScheme X]
    (V : SchemeDivisorPoint X)
    (F L : Type*) [Field F] [Field L]
    [CharP (X.presheaf.stalk V.1) p]
    [Algebra (X.presheaf.stalk V.1) F]
    [IsFractionRing (X.presheaf.stalk V.1) F]
    [Algebra F L] [IsGalois F L] [FiniteDimensional F L]
    [Algebra (X.presheaf.stalk V.1) L]
    [IsScalarTower (X.presheaf.stalk V.1) F L]
    (hdegree : (Module.finrank F L).Coprime p) :
    Stacks.SchemeLevel.IsTamelyRamifiedOver (X.presheaf.stalk V.1) L := by
  letI : IsDiscreteValuationRing (X.presheaf.stalk V.1) :=
    V.stalk_isDiscreteValuationRing
  exact galois_isTamelyRamifiedOver p hp (X.presheaf.stalk V.1) F L hdegree

#print axioms galois_integralClosure_isTamelyRamifiedAt
#print axioms isFractionRing_targetGenericStalk_of_finiteDominant
#print axioms primeToP_specialization_of_galois_integralClosure
#print axioms primeToP_specialization_isTamelyRamifiedAt
#print axioms primeToP_specialization_isTamelyRamifiedInCodimensionOneAlong
#print axioms finiteNormalCover_isTamelyRamifiedInCodimensionOneAlong
#print axioms finiteNormalAffinePreimage_isTamelyRamifiedInCodimensionOneAlong
#print axioms finiteNormalCover_isTamelyRamifiedAt_of_heightOne
#print axioms finiteNormalCover_isTamelyRamifiedInCodimensionOneAlong_of_noetherian
#print axioms finiteNormalCover_localization_isTamelyRamifiedInCodimensionOneAlong
#print axioms finiteNormalAffinePreimage_localization_isTamelyRamifiedInCodimensionOneAlong
#print axioms tameLocalBoundingChart_ofFiniteNormalAffinePreimage
#print axioms galois_integralClosure_isTamelyRamifiedInCodimensionOneAlong
#print axioms galois_isTamelyRamifiedOver
#print axioms galois_schemeDivisorStalk_isTamelyRamifiedOver

end Pcf
