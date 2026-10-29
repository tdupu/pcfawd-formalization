/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPPrimaryFibresField
public import Pcf.Bounding.PaperPPrimaryFibresSquare
public import Pcf.Bounding.PrimaryNormalizationFinite
public import Pcf.Bounding.SchemePrimaryLocalizedDelta
public import Pcf.Bounding.SchemePrimaryLocalizedResidue
public import Pcf.Bounding.PrimaryResidueAllPrimes
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The actual square of `lem:primary-fibres` on affine charts

`paper-p.tex`, proof of Lemma `lem:primary-fibres` (live source l. 1233–1276):

> Put `K=k(B)` and `L=k(E)`. Choose a finite purely inseparable `K'/K` such that the reduction
> of the generic fibre after base change is geometrically reduced. Its function field `L'=LK'`
> is geometrically reduced over `K'`. Write `[K':K]=p^a`. Let `B'` be the normalization of `B`
> in `K'`, and `E'` the normalization of `(E×_B B')_red`. [...] Comparing orders of `t` around
> the square gives `e(F'/F) v_F(q^*t) = e(D'/D) v_{F'}(q'^*t') = e(D'/D)`. [...] reduction
> modulo `t` gives `e(D'/D)[κ(D'):κ(D)] = p^a`. Hence `v_F(q^*t)` is a power of `p` dividing
> `p^a`.

Construction, on affine charts `B = Spec A`, `E ⊇ Spec R` (`A → R` injective, finite type,
normal domains of finite type over `k`). All fields live in `Ω = \overline{Frac R}`:
* `K = Frac A`, `L = Frac R`; `K' = K(T)` (`baseAlt`) for a finite `T ⊆ Ω` of elements purely
  inseparable over `K`; `L' = L(T)` (`sourceAlt`), which equals the compositum `K'(X) = LK'`
  (`sourceAlt_toSubfield_eq`, `X` = images of generators of `R`).
* `A' = ` integral closure of `A` in `K'` (`baseNorm`, the chart of `B'`); `R' = ` integral
  closure of `R` in `L'` (`sourceNorm`, the chart of `E'`). Since `R ⊗_A A'` is integral over
  `R` with total ring of fractions reducing to `L'`, `R'` is the normalization of
  `(R ⊗_A A')_red`, i.e. the chart of `E'`.
* the square `A → A' → R'`, `A → R → R'` (`normToNorm`, `IsScalarTower` instances).

`exists_primaryFibres_paperSquare` instantiates `primaryFibres_square_display` on this actual
square. The base estimate `e(D'/D) ∣ p^a` is `integralClosure_ramificationIdx_dvd_finrank`
(fundamental identity `e(D'/D)·[κ(D'):κ(D)]_{insep} = [K':K]` at the DVR `A_D`).

Divergences: formal smoothness of `L'/K'` replaces geometric reducedness, and reduced fibres
over a dense open come from openness of the smooth locus rather than Stacks `0578` (see
`PaperPPrimaryFibresField` and `PaperPPrimaryFibresSquare`).
-/

@[expose] public section

namespace Pcf.Bounding.PaperPPrimaryFibres

set_option linter.style.haveILetI false

universe u

open IntermediateField

noncomputable section

/-- **`e(D'/D) ∣ [K':K]`.** For the normalization `A'` of `A` in a finite purely inseparable
`K'/K`, the ramification index of a prime `D'` over a height-one `D` divides `[K':K]`
(the paper: "the normalization of the discrete valuation ring at `D` in `K'` is finite free of
rank `p^a`; reduction modulo `t` gives `e(D'/D)[κ(D'):κ(D)] = p^a`"). -/
theorem integralClosure_ramificationIdx_dvd_finrank (k : Type u) [Field k] (pchar : ℕ)
    [hp : Fact pchar.Prime] [CharP k pchar]
    (A K K' : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    [Algebra k A] [Algebra.FiniteType k A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Field K'] [Algebra K K'] [Algebra A K']
    [IsScalarTower A K K'] [FiniteDimensional K K'] [IsPurelyInseparable K K']
    (D : Ideal A) [D.IsPrime] (hD : D.height = 1)
    (D' : Ideal (integralClosure A K')) [D'.IsPrime] [D'.LiesOver D] :
    D'.ramificationIdx A ∣ Module.finrank K K' := by
  let Rp := Localization.AtPrime D
  haveI : IsDiscreteValuationRing Rp :=
    isDiscreteValuationRing_localizationAtPrime_of_heightOne D hD
  letI : Algebra Rp K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe Rp K
      D.primeCompl (nonZeroDivisors A) D.primeCompl_le_nonZeroDivisors
  letI : IsScalarTower A Rp K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le Rp K
      D.primeCompl (nonZeroDivisors A) D.primeCompl_le_nonZeroDivisors
  letI : IsFractionRing Rp K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization D.primeCompl Rp K
  letI : Algebra Rp K' := ((algebraMap K K').comp (algebraMap Rp K)).toAlgebra
  letI : IsScalarTower Rp K K' := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A Rp K' := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply A K K']
    change algebraMap K K' (algebraMap A K r) =
      algebraMap K K' (algebraMap Rp K (algebraMap A Rp r))
    rw [← IsScalarTower.algebraMap_apply A Rp K])
  have hinj : Function.Injective (algebraMap A K') := by
    rw [IsScalarTower.algebraMap_eq A K K']
    exact (algebraMap K K').injective.comp (IsFractionRing.injective A K)
  haveI : Module.Finite A (integralClosure A K') :=
    Bounding.PrimaryFibres.finite_integralClosure_in_finite_extension k A K K'
  have hp0 : IsLocalRing.maximalIdeal Rp ≠ ⊥ :=
    (IsLocalRing.isField_iff_maximalIdeal_eq (R := Rp)).not.mp
      (IsLocalization.AtPrime.not_isField A (Ideal.ne_bot_of_height_eq_one hD) Rp)
  haveI : CharP A pchar := charP_of_injective_algebraMap (algebraMap k A).injective pchar
  haveI : CharP K pchar := charP_of_injective_algebraMap (IsFractionRing.injective A K) pchar
  haveI : ExpChar K pchar := (expChar_prime_iff K hp.out).mpr inferInstance
  haveI : CharP D.ResidueField pchar :=
    CharP.of_ringHom_of_ne_zero (algebraMap A D.ResidueField) pchar hp.out.ne_zero
  haveI : ExpChar D.ResidueField pchar := (expChar_prime_iff _ hp.out).mpr inferInstance
  letI : ExpChar (IsLocalRing.maximalIdeal Rp).ResidueField pchar :=
    (residueFieldEquivOfLocalizationAtPrime A Rp D).symm.toRingHom.expChar
      (residueFieldEquivOfLocalizationAtPrime A Rp D).symm.injective pchar
  letI := Localization.AtPrime.algebraOfLiesOver D D'
  have hpure : IsPurelyInseparable D.ResidueField D'.ResidueField :=
    Bounding.PrimaryFibres.integralClosure_residueField_isPurelyInseparable_at_prime
      A K K' D D' pchar
  have h := integralClosure_delta_eq_genericDegree_atPrime A Rp K K' D hinj pchar hp0 D' hpure
  exact Dvd.intro _ h


section Construction

variable (A R : Type u) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R]
  [FaithfulSMul A R]

/-- The algebraically closed field `Ω ⊇ L = Frac R` holding all function fields. -/
abbrev PaperOmega := AlgebraicClosure (FractionRing R)

instance : FaithfulSMul A (FractionRing R) := FaithfulSMul.trans A R _

/-- `K = Frac A ⊆ L = Frac R`. -/
scoped instance fracAlgebra : Algebra (FractionRing A) (FractionRing R) :=
  FractionRing.liftAlgebra A _

open scoped Pcf.Bounding.PaperPPrimaryFibres

variable (T : Finset (PaperOmega R))

/-- `K' = K(T)`. -/
abbrev baseAlt : IntermediateField (FractionRing A) (PaperOmega R) :=
  adjoin (FractionRing A) (T : Set (PaperOmega R))
/-- `L' = L(T) = LK'`. -/
abbrev sourceAlt : IntermediateField (FractionRing R) (PaperOmega R) :=
  adjoin (FractionRing R) (T : Set (PaperOmega R))
/-- `A'`: the normalization of `A` in `K'` (affine chart of `B'`). -/
abbrev baseNorm := integralClosure A (baseAlt A R T)
/-- `R'`: the normalization of `R` in `L'` (affine chart of `E'`). -/
abbrev sourceNorm := integralClosure R (sourceAlt R T)

omit [IsDomain A] in
theorem algebraMap_frac_coe (x : FractionRing A) :
    algebraMap (FractionRing A) (PaperOmega R) x =
      algebraMap (FractionRing R) (PaperOmega R) (algebraMap (FractionRing A) (FractionRing R) x) :=
  IsScalarTower.algebraMap_apply _ _ _ x

theorem baseAlt_le {x : PaperOmega R} (hx : x ∈ baseAlt A R T) : x ∈ sourceAlt R T := by
  have h : (baseAlt A R T).toSubfield ≤ (sourceAlt R T).toSubfield := by
    rw [adjoin_toSubfield]
    refine Subfield.closure_le.mpr (Set.union_subset ?_ ?_)
    · rintro _ ⟨y, rfl⟩
      rw [algebraMap_frac_coe]
      exact (sourceAlt R T).algebraMap_mem _
    · exact subset_adjoin (FractionRing R) (T : Set (PaperOmega R))
  exact h hx

/-- The inclusion `K' → L'`. -/
def baseToSource : baseAlt A R T →+* sourceAlt R T :=
  (baseAlt A R T).val.toRingHom.codRestrict (sourceAlt R T) fun x => baseAlt_le A R T x.2

theorem coe_baseToSource (x : baseAlt A R T) :
    ((baseToSource A R T x : sourceAlt R T) : PaperOmega R) = x :=
  (RingHom.codRestrict_apply _ _ _ _).trans (show (baseAlt A R T).val x = x from rfl)

scoped instance : Algebra (baseAlt A R T) (sourceAlt R T) := (baseToSource A R T).toAlgebra

theorem coe_algebraMap_baseAlt_sourceAlt (x : baseAlt A R T) :
    ((algebraMap (baseAlt A R T) (sourceAlt R T) x : sourceAlt R T) : PaperOmega R) = x :=
  coe_baseToSource A R T x

theorem coe_algebraMap_A_baseAlt (a : A) :
    ((algebraMap A (baseAlt A R T) a : baseAlt A R T) : PaperOmega R) =
      algebraMap A (PaperOmega R) a := rfl

omit [IsDomain A] [FaithfulSMul A R] in
theorem coe_algebraMap_A_sourceAlt (a : A) :
    ((algebraMap A (sourceAlt R T) a : sourceAlt R T) : PaperOmega R) =
      algebraMap A (PaperOmega R) a := rfl

theorem coe_algebraMap_R_sourceAlt (r : R) :
    ((algebraMap R (sourceAlt R T) r : sourceAlt R T) : PaperOmega R) =
      algebraMap R (PaperOmega R) r := rfl

instance : IsScalarTower A (baseAlt A R T) (PaperOmega R) :=
  .of_algebraMap_eq fun a => (coe_algebraMap_A_baseAlt A R T a).symm

instance : IsScalarTower A R (sourceAlt R T) := .of_algebraMap_eq fun a => Subtype.ext (by
  rw [coe_algebraMap_A_sourceAlt, coe_algebraMap_R_sourceAlt,
    IsScalarTower.algebraMap_apply A R (PaperOmega R)])

/-- `K' → L'` as an `A`-algebra map. -/
def baseToSourceAlgHom : baseAlt A R T →ₐ[A] sourceAlt R T where
  __ := baseToSource A R T
  commutes' a := Subtype.ext (by
    change ((baseToSource A R T _ : sourceAlt R T) : PaperOmega R) = _
    rw [coe_baseToSource, coe_algebraMap_A_baseAlt, coe_algebraMap_A_sourceAlt])

theorem isIntegral_baseToSource (x : baseNorm A R T) :
    IsIntegral R (baseToSource A R T x.1) :=
  (x.2.map (baseToSourceAlgHom A R T)).tower_top

/-- `A' → R'`. -/
def normToNorm : baseNorm A R T →+* sourceNorm R T :=
  ((baseToSource A R T).comp (baseNorm A R T).val.toRingHom).codRestrict
    ((sourceNorm R T).toSubsemiring) (fun x => isIntegral_baseToSource A R T x)

scoped instance : Algebra (baseNorm A R T) (sourceNorm R T) := (normToNorm A R T).toAlgebra

theorem coe_algebraMap_norm (x : baseNorm A R T) :
    (((algebraMap (baseNorm A R T) (sourceNorm R T) x : sourceNorm R T) : sourceAlt R T) :
      PaperOmega R) = ((x : baseAlt A R T) : PaperOmega R) := by
  change (((normToNorm A R T x : sourceNorm R T) : sourceAlt R T) : PaperOmega R) = _
  rw [show ((normToNorm A R T x : sourceNorm R T) : sourceAlt R T) =
      baseToSource A R T (x : baseAlt A R T) from RingHom.codRestrict_apply _ _ _ _,
    coe_baseToSource]

instance : IsScalarTower A (baseNorm A R T) (sourceNorm R T) := .of_algebraMap_eq fun a => by
  apply Subtype.ext; apply Subtype.ext
  rw [coe_algebraMap_norm]
  change ((algebraMap A (baseAlt A R T) a : baseAlt A R T) : PaperOmega R) =
    ((algebraMap A (sourceAlt R T) a : sourceAlt R T) : PaperOmega R)
  rw [coe_algebraMap_A_baseAlt, coe_algebraMap_A_sourceAlt]

end Construction

section Properties

variable (A R : Type u) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R]
  [FaithfulSMul A R] (T : Finset (PaperOmega R))
  (hT : (T : Set (PaperOmega R)) ⊆ perfectClosure (FractionRing A) (PaperOmega R))

open scoped Pcf.Bounding.PaperPPrimaryFibres

include hT in
theorem baseAlt_isPurelyInseparable : IsPurelyInseparable (FractionRing A) (baseAlt A R T) :=
  (le_perfectClosure_iff _ _ _).mp (adjoin_le_iff.mpr hT)

include hT in
theorem baseAlt_finiteDimensional : FiniteDimensional (FractionRing A) (baseAlt A R T) := by
  haveI := baseAlt_isPurelyInseparable A R T hT
  refine finiteDimensional_adjoin fun x hx => ?_
  have : IsIntegral (FractionRing A) (⟨x, subset_adjoin _ _ hx⟩ : baseAlt A R T) :=
    IsPurelyInseparable.isIntegral' _ _
  exact this.map (baseAlt A R T).val

include hT in
theorem sourceAlt_finiteDimensional : FiniteDimensional (FractionRing R) (sourceAlt R T) := by
  haveI := baseAlt_isPurelyInseparable A R T hT
  refine finiteDimensional_adjoin fun x hx => ?_
  have : IsIntegral (FractionRing A) (⟨x, subset_adjoin _ _ hx⟩ : baseAlt A R T) :=
    IsPurelyInseparable.isIntegral' _ _
  exact (this.map (baseAlt A R T).val).tower_top

omit [IsDomain A] [FaithfulSMul A R] in
theorem algebraMap_R_omega_injective : Function.Injective (algebraMap R (PaperOmega R)) := by
  rw [IsScalarTower.algebraMap_eq R (FractionRing R) (PaperOmega R)]
  exact (algebraMap (FractionRing R) (PaperOmega R)).injective.comp
    (IsFractionRing.injective R (FractionRing R))

omit [IsDomain A] in
theorem algebraMap_A_omega_injective : Function.Injective (algebraMap A (PaperOmega R)) := by
  rw [IsScalarTower.algebraMap_eq A R (PaperOmega R)]
  exact (algebraMap_R_omega_injective R).comp (FaithfulSMul.algebraMap_injective A R)

theorem algebraMap_A_baseNorm_injective : Function.Injective (algebraMap A (baseNorm A R T)) := by
  intro a b h
  have h' := congrArg (fun x : baseNorm A R T => ((x : baseAlt A R T) : PaperOmega R)) h
  change algebraMap A (PaperOmega R) a = algebraMap A (PaperOmega R) b at h'
  exact algebraMap_A_omega_injective A R h'

theorem algebraMap_R_sourceNorm_injective :
    Function.Injective (algebraMap R (sourceNorm R T)) := by
  intro a b h
  have h' := congrArg (fun x : sourceNorm R T => ((x : sourceAlt R T) : PaperOmega R)) h
  change algebraMap R (PaperOmega R) a = algebraMap R (PaperOmega R) b at h'
  exact algebraMap_R_omega_injective R h'

theorem algebraMap_norm_injective :
    Function.Injective (algebraMap (baseNorm A R T) (sourceNorm R T)) := by
  intro a b h
  have h' := congrArg (fun x : sourceNorm R T => ((x : sourceAlt R T) : PaperOmega R)) h
  simp only [coe_algebraMap_norm] at h'
  exact Subtype.ext (Subtype.ext h')

instance : FaithfulSMul A (baseNorm A R T) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap_A_baseNorm_injective A R T)
instance : FaithfulSMul R (sourceNorm R T) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap_R_sourceNorm_injective R T)
instance : FaithfulSMul (baseNorm A R T) (sourceNorm R T) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap_norm_injective A R T)

include hT in
theorem baseNorm_isIntegrallyClosed : IsIntegrallyClosed (baseNorm A R T) := by
  haveI := baseAlt_finiteDimensional A R T hT
  exact integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing A)

include hT in
theorem sourceNorm_isIntegrallyClosed : IsIntegrallyClosed (sourceNorm R T) := by
  haveI := sourceAlt_finiteDimensional A R T hT
  exact integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R)

variable (k : Type u) [Field k] [Algebra k A] [Algebra.FiniteType k A] [Algebra k R]
  [IsScalarTower k A R] [Algebra.FiniteType A R]

include k

omit [Algebra k R] [IsScalarTower k A R] [Algebra.FiniteType A R] in
include hT in
theorem baseNorm_finite : Module.Finite A (baseNorm A R T) := by
  haveI := baseAlt_finiteDimensional A R T hT
  exact PrimaryFibres.finite_integralClosure_in_finite_extension k A (FractionRing A) _

include hT in
theorem sourceNorm_finite : Module.Finite R (sourceNorm R T) := by
  haveI := sourceAlt_finiteDimensional A R T hT
  haveI : Algebra.FiniteType k R := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  exact PrimaryFibres.finite_integralClosure_in_finite_extension k R (FractionRing R) _

include hT in
theorem norm_finitePresentation :
    Algebra.FinitePresentation (baseNorm A R T) (sourceNorm R T) := by
  haveI := baseNorm_finite A R T hT k
  haveI := sourceNorm_finite A R T hT k
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  haveI : IsNoetherianRing (baseNorm A R T) := Algebra.FiniteType.isNoetherianRing A _
  haveI : Algebra.FiniteType A (sourceNorm R T) :=
    Algebra.FiniteType.trans (S := R) inferInstance inferInstance
  haveI : Algebra.FiniteType (baseNorm A R T) (sourceNorm R T) :=
    Algebra.FiniteType.of_restrictScalars_finiteType A _ _
  exact Algebra.FinitePresentation.of_finiteType.mp inferInstance

end Properties

section Smooth

variable (A R : Type u) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R]
  [FaithfulSMul A R] (T : Finset (PaperOmega R)) (s : Finset R)
  (hs : Algebra.adjoin A (s : Set R) = ⊤)

open scoped Pcf.Bounding.PaperPPrimaryFibres

open scoped Classical in
/-- The finite set `X ⊆ Ω` of generators of `L = K(X)`: images of generators of `R` over `A`. -/
abbrev genImage : Finset (PaperOmega R) := s.image (algebraMap R (PaperOmega R))

include hs in
/-- `L' = L(T)` equals `K'(X)` as a subfield of `Ω`: the source alteration is the compositum. -/
theorem sourceAlt_toSubfield_eq :
    (sourceAlt R T).toSubfield =
      (adjoin (baseAlt A R T) ((genImage R s : Finset _) : Set (PaperOmega R))).toSubfield := by
  set M := adjoin (baseAlt A R T) ((genImage R s : Finset _) : Set (PaperOmega R))
  -- the image of `R` lies in `K'(X)`
  have hR : ∀ r : R, algebraMap R (PaperOmega R) r ∈ M := by
    intro r
    have hr : r ∈ Algebra.adjoin A (s : Set R) := hs ▸ Algebra.mem_top
    let φ : R →ₐ[A] PaperOmega R := IsScalarTower.toAlgHom A R (PaperOmega R)
    have hle : Algebra.adjoin A (φ '' (s : Set R)) ≤ M.toSubalgebra.restrictScalars A := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨x, hx, rfl⟩
      exact subset_adjoin _ _ (by simpa [genImage] using ⟨x, hx, rfl⟩)
    have : φ r ∈ Algebra.adjoin A (φ '' (s : Set R)) := by
      rw [← AlgHom.map_adjoin]; exact ⟨r, hr, rfl⟩
    exact hle this
  apply le_antisymm
  · rw [adjoin_toSubfield]
    refine Subfield.closure_le.mpr (Set.union_subset ?_ ?_)
    · rintro _ ⟨y, rfl⟩
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) y
      rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
      exact M.div_mem (hR a) (hR b)
    · intro t ht
      exact M.algebraMap_mem ⟨t, subset_adjoin _ _ ht⟩
  · rw [adjoin_toSubfield]
    refine Subfield.closure_le.mpr (Set.union_subset ?_ ?_)
    · rintro _ ⟨y, rfl⟩
      exact baseAlt_le A R T y.2
    · intro x hx
      simp only [genImage, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨r, -, rfl⟩ := hx
      rw [IsScalarTower.algebraMap_apply R (FractionRing R) (PaperOmega R)]
      exact (sourceAlt R T).algebraMap_mem _

include hs in
/-- Formal smoothness of `K'(X)/K'` transfers to `L'/K'`. -/
theorem sourceAlt_formallySmooth
    [hsm : Algebra.FormallySmooth (baseAlt A R T)
      (adjoin (baseAlt A R T) ((genImage R s : Finset _) : Set (PaperOmega R)))] :
    Algebra.FormallySmooth (baseAlt A R T) (sourceAlt R T) := by
  set M := adjoin (baseAlt A R T) ((genImage R s : Finset _) : Set (PaperOmega R))
  have heq := sourceAlt_toSubfield_eq A R T s hs
  have hmem : ∀ x : M, (x : PaperOmega R) ∈ sourceAlt R T := fun x => by
    have : (x : PaperOmega R) ∈ M.toSubfield := x.2
    rw [← heq] at this; exact this
  have hmem' : ∀ x : sourceAlt R T, (x : PaperOmega R) ∈ M := fun x => by
    have : (x : PaperOmega R) ∈ (sourceAlt R T).toSubfield := x.2
    rw [heq] at this; exact this
  let f : M →+* sourceAlt R T := M.val.toRingHom.codRestrict (sourceAlt R T) hmem
  have hf : ∀ x : M, ((f x : sourceAlt R T) : PaperOmega R) = x := fun x =>
    (RingHom.codRestrict_apply _ _ _ _).trans (show M.val x = x from rfl)
  let e : M ≃+* sourceAlt R T :=
    RingEquiv.ofBijective f ⟨fun x y h => Subtype.ext (by
      have := congrArg (fun z : sourceAlt R T => (z : PaperOmega R)) h
      simpa only [hf] using this), fun y => ⟨⟨y, hmem' y⟩, Subtype.ext (hf _)⟩⟩
  let e' : M ≃ₐ[baseAlt A R T] sourceAlt R T :=
    AlgEquiv.ofRingEquiv (f := e) fun c => Subtype.ext (by
      change ((f _ : sourceAlt R T) : PaperOmega R) = _
      rw [hf, coe_algebraMap_baseAlt_sourceAlt]; rfl)
  exact Algebra.FormallySmooth.of_equiv e'

set_option synthInstance.maxHeartbeats 400000 in
-- Instance search for `SMul`/`IsScalarTower` on localizations of `R'` explores the
-- intermediate-field algebra instances of `Ω` and exceeds the default budget.
include hs in
/-- **The altered morphism is smooth at the generic point of `E'`.** -/
theorem norm_isSmoothAt_bot
    (hT : (T : Set (PaperOmega R)) ⊆ perfectClosure (FractionRing A) (PaperOmega R))
    [Algebra.FormallySmooth (baseAlt A R T)
      (adjoin (baseAlt A R T) ((genImage R s : Finset _) : Set (PaperOmega R)))] :
    Algebra.IsSmoothAt (baseNorm A R T) (⊥ : Ideal (sourceNorm R T)) := by
  haveI := baseAlt_finiteDimensional A R T hT
  haveI := sourceAlt_finiteDimensional A R T hT
  haveI := sourceAlt_formallySmooth A R T s hs
  haveI : IsFractionRing (baseNorm A R T) (baseAlt A R T) :=
    integralClosure.isFractionRing_of_finite_extension (FractionRing A) _
  haveI : IsFractionRing (sourceNorm R T) (sourceAlt R T) :=
    integralClosure.isFractionRing_of_finite_extension (FractionRing R) _
  -- `A' → K'` is a localization, hence formally smooth
  haveI : Algebra.FormallySmooth (baseNorm A R T) (baseAlt A R T) :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors (baseNorm A R T))
  letI : Algebra (baseNorm A R T) (sourceAlt R T) :=
    ((algebraMap (sourceNorm R T) (sourceAlt R T)).comp
      (algebraMap (baseNorm A R T) (sourceNorm R T))).toAlgebra
  haveI : IsScalarTower (baseNorm A R T) (sourceNorm R T) (sourceAlt R T) :=
    .of_algebraMap_eq' rfl
  have hsc : IsScalarTower (baseNorm A R T) (baseAlt A R T) (sourceAlt R T) :=
    .of_algebraMap_eq fun x => Subtype.ext (by
      change (((algebraMap (baseNorm A R T) (sourceNorm R T) x : sourceNorm R T) : sourceAlt R T) :
        PaperOmega R) = _
      rw [coe_algebraMap_norm, coe_algebraMap_baseAlt_sourceAlt]; rfl)
  haveI : Algebra.FormallySmooth (baseNorm A R T) (sourceAlt R T) :=
    @Algebra.FormallySmooth.comp (baseNorm A R T) _ (baseAlt A R T) _ _ (sourceAlt R T) _ _ _ hsc
      inferInstance inferInstance
  haveI : IsLocalization (⊥ : Ideal (sourceNorm R T)).primeCompl (sourceAlt R T) := by
    rw [Ideal.primeCompl_bot]
    exact (inferInstance : IsFractionRing (sourceNorm R T) (sourceAlt R T))
  have e := IsLocalization.algEquiv (⊥ : Ideal (sourceNorm R T)).primeCompl
    (Localization.AtPrime (⊥ : Ideal (sourceNorm R T))) (sourceAlt R T)
  exact Algebra.FormallySmooth.of_equiv (AlgEquiv.ofRingEquiv (f := e.symm.toRingEquiv)
    (fun x => by
      change e.symm (algebraMap (sourceNorm R T) (sourceAlt R T)
        (algebraMap (baseNorm A R T) (sourceNorm R T) x)) = _
      rw [AlgEquiv.commutes]
      exact (IsScalarTower.algebraMap_apply _ _ _ x).symm))

end Smooth

section Main

open scoped Pcf.Bounding.PaperPPrimaryFibres

set_option synthInstance.maxHeartbeats 400000 in
-- Instance search for `SMul`/`IsScalarTower` on localizations of `R'` explores the
-- intermediate-field algebra instances of `Ω` and exceeds the default budget.
/-- **The paper's proof of `lem:primary-fibres`, affine form.** Let `k` have characteristic
`p`, `A → R` an injective finite-type map of normal domains of finite type over `k`
(`q : E → B` on affine charts), `K = Frac A`, `L = Frac R`. There is a finite set `T ⊆ Ω` such
that `K' = K(T)` is finite purely inseparable over `K`, `[K':K] = p^a`, and, with
`A' = baseNorm A R T` (normalization of `A` in `K'`) and `R' = sourceNorm R T` (normalization of
`R` in `L' = LK'`), `R'` is smooth over `A'` at its generic point; and there is `c ≠ 0` in `A`
such that for every height-one `D ∌ c` of `A` and every height-one `F` of `R` over `D`, there are
height-one `D'`, `F'` of `A'`, `R'` over `D`, `F` (`F'` over `D'`) with
`v_{F'}(q'^* t') = 1`, `e(F'/F) · v_F(q^* t) = e(D'/D) · v_{F'}(q'^* t') = e(D'/D)`, and
`v_F(q^* t) = p^b` with `b ≤ a`. -/
theorem exists_primaryFibres_paperSquare (p : ℕ) [hp : Fact p.Prime]
    (k : Type u) [Field k] [CharP k p]
    (A R : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra k A]
    [Algebra.FiniteType k A] [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Algebra k R]
    [Algebra A R] [IsScalarTower k A R] [FaithfulSMul A R] [Algebra.FiniteType A R] :
    ∃ T : Finset (PaperOmega R),
      IsPurelyInseparable (FractionRing A) (baseAlt A R T) ∧
      ∃ a : ℕ, Module.finrank (FractionRing A) (baseAlt A R T) = p ^ a ∧
      Algebra.IsSmoothAt (baseNorm A R T) (⊥ : Ideal (sourceNorm R T)) ∧
      ∃ c : A, c ≠ 0 ∧ ∀ (D : Ideal A) [D.IsPrime], D.height = 1 → c ∉ D →
        ∀ (F : Ideal R) [F.IsPrime], F.height = 1 → F.LiesOver D →
          ∃ (D' : Ideal (baseNorm A R T)) (F' : Ideal (sourceNorm R T))
            (_ : D'.IsPrime) (_ : F'.IsPrime),
            D'.height = 1 ∧ F'.height = 1 ∧ D'.LiesOver D ∧ F'.LiesOver F ∧ F'.LiesOver D' ∧
            F'.ramificationIdx (baseNorm A R T) = 1 ∧
            F'.ramificationIdx R * F.ramificationIdx A =
              D'.ramificationIdx A * F'.ramificationIdx (baseNorm A R T) ∧
            D'.ramificationIdx A * F'.ramificationIdx (baseNorm A R T) = D'.ramificationIdx A ∧
            ∃ b ≤ a, F.ramificationIdx A = p ^ b := by
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra A R).FG)
  obtain ⟨T, hT, -, hpi, hsm⟩ := exists_finite_purelyInseparable_formallySmooth_adjoin
    (FractionRing A) (PaperOmega R) (genImage R s)
  haveI := hsm
  haveI : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
  haveI : CharP (FractionRing A) p :=
    charP_of_injective_algebraMap (IsFractionRing.injective A (FractionRing A)) p
  haveI : ExpChar (FractionRing A) p := (expChar_prime_iff _ hp.out).mpr inferInstance
  haveI := baseAlt_finiteDimensional A R T hT
  obtain ⟨a, ha⟩ := IsPurelyInseparable.finrank_eq_pow (FractionRing A) (baseAlt A R T) p
  have hsmooth := norm_isSmoothAt_bot A R T s hs hT
  refine ⟨T, hpi, a, ha, hsmooth, ?_⟩
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  haveI : Algebra.FiniteType k R := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  haveI := baseNorm_finite A R T hT k
  haveI := sourceNorm_finite A R T hT k
  haveI : IsNoetherianRing (baseNorm A R T) := Algebra.FiniteType.isNoetherianRing A _
  haveI : IsNoetherianRing (sourceNorm R T) := Algebra.FiniteType.isNoetherianRing R _
  haveI := baseNorm_isIntegrallyClosed A R T hT
  haveI := sourceNorm_isIntegrallyClosed A R T hT
  haveI := norm_finitePresentation A R T hT k
  have hbase : ∀ (D : Ideal A) [D.IsPrime], D.height = 1 →
      ∀ (D' : Ideal (baseNorm A R T)) [D'.IsPrime], D'.LiesOver D →
        D'.ramificationIdx A ∣ p ^ a := by
    intro D _ hD D' _ hD'
    rw [← ha]
    exact integralClosure_ramificationIdx_dvd_finrank k p A (FractionRing A) (baseAlt A R T)
      D hD D'
  obtain ⟨c, hc0, hc⟩ := primaryFibres_square_display (R := R) p a hsmooth hbase
  refine ⟨c, hc0, ?_⟩
  intro D _ hD hcD F _ hF hFD
  obtain ⟨D', F', hD'p, hF'p, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hc D hD hcD F hF hFD
  exact ⟨D', F', hD'p, hF'p, h1, h2, h3, h4, h5, h6, h7, h8,
    (Nat.dvd_prime_pow hp.out).mp h9⟩

end Main

end

end Pcf.Bounding.PaperPPrimaryFibres

#print axioms Pcf.Bounding.PaperPPrimaryFibres.integralClosure_ramificationIdx_dvd_finrank
#print axioms Pcf.Bounding.PaperPPrimaryFibres.sourceAlt_toSubfield_eq
#print axioms Pcf.Bounding.PaperPPrimaryFibres.norm_isSmoothAt_bot
#print axioms Pcf.Bounding.PaperPPrimaryFibres.exists_primaryFibres_paperSquare
