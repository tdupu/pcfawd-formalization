/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Bounding.RegularLocus
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Algebraic prerequisites for a finite-type regular-locus theorem

This module proves localization stability for regular rings, constructs finite
presentations over regular polynomial rings, and relates affine regularity to
the actual scheme stalks used by `stalkSingularLocus`.

The general finite-type regular-locus theorem is not proved here. In particular,
finite presentation by a regular ambient ring does not by itself prove openness
of the regular locus of its quotient. The missing commutative-algebra step is
recorded precisely in `isOpen_primeRegularLocus_iff`: a regular localization of
a finite-type algebra must have a principal neighborhood of regular points.
The informal general theorem is Stacks Project, Tags `07PJ` and `07R5`.
-/

universe u v

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

/-- Regularity of local rings is invariant under an arbitrary ring equivalence. -/
theorem isRegularLocalRing_iff_of_ringEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (e : R ≃+* S) :
    IsRegularLocalRing R ↔ IsRegularLocalRing S := by
  constructor <;> intro h
  · exact IsRegularLocalRing.of_ringEquiv e
  · exact IsRegularLocalRing.of_ringEquiv e.symm

/-- A prime localization of a localization is regular exactly when the original
ring localized at the contracted prime is regular. -/
theorem isRegularLocalRing_localizationAtPrime_iff
    {R : Type u} [CommRing R]
    (M : Submonoid R) (S : Type v) [CommRing S] [Algebra R S]
    [IsLocalization M S] (p : Ideal S) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) ↔
      IsRegularLocalRing (Localization.AtPrime (p.comap (algebraMap R S))) := by
  let q := p.comap (algebraMap R S)
  let : q.IsPrime := p.comap_isPrime _
  let : IsLocalization.AtPrime (Localization.AtPrime p) q :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      M (Localization.AtPrime p) p
  exact isRegularLocalRing_iff_of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl
      (Localization.AtPrime p) (Localization.AtPrime q)).toRingEquiv

/-- Localizing a regular ring preserves regularity. This does not assert the
deeper theorem that every regular local ring is a regular ring. -/
theorem isRegularRing_of_isLocalization
    {R : Type u} [CommRing R] [IsRegularRing R]
    (M : Submonoid R) (S : Type v) [CommRing S] [Algebra R S]
    [IsLocalization M S] : IsRegularRing S := by
  let : IsNoetherianRing S := IsLocalization.isNoetherianRing M S inferInstance
  apply isRegularRing_iff.mpr
  intro p hp
  exact (isRegularLocalRing_localizationAtPrime_iff M S p).mpr inferInstance

/-- A finite-type algebra over a field is a finitely presented quotient of a
regular polynomial ring. The conclusion does not assert that the quotient is
regular. -/
theorem finiteType_exists_regular_presentation
    (k : Type u) [Field k] (R : Type v) [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] :
    ∃ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k)),
      I.FG ∧ IsRegularRing (MvPolynomial (Fin n) k) ∧
      Nonempty ((MvPolynomial (Fin n) k ⧸ I) ≃ₐ[k] R) := by
  let : Algebra.FinitePresentation k R :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨n, I, e, hI⟩ := Algebra.FinitePresentation.iff.mp
    (inferInstance : Algebra.FinitePresentation k R)
  exact ⟨n, I, hI, inferInstance, ⟨e⟩⟩

/-- The pointwise regular locus of an affine ring. -/
def primeRegularLocus (R : Type u) [CommRing R] : Set (PrimeSpectrum R) :=
  {p | IsRegularLocalRing (Localization.AtPrime p.asIdeal)}

/-- Affine regular loci pull back exactly along localization maps. -/
theorem preimage_primeRegularLocus_of_isLocalization
    {R : Type u} [CommRing R]
    (M : Submonoid R) (S : Type v) [CommRing S] [Algebra R S]
    [IsLocalization M S] :
    PrimeSpectrum.comap (algebraMap R S) ⁻¹' primeRegularLocus R =
      primeRegularLocus S := by
  ext p
  exact (isRegularLocalRing_localizationAtPrime_iff M S p.asIdeal).symm

/-- The exact principal-neighborhood criterion for openness of the regular locus.
Proving its right-hand side for finite-type algebras is the remaining algebraic
obligation; no such implication is assumed by this module. -/
theorem isOpen_primeRegularLocus_iff (R : Type u) [CommRing R] :
    IsOpen (primeRegularLocus R) ↔
      ∀ (p : PrimeSpectrum R),
        IsRegularLocalRing (Localization.AtPrime p.asIdeal) →
        ∃ f : R, f ∉ p.asIdeal ∧ ∀ (q : PrimeSpectrum R),
          f ∉ q.asIdeal → IsRegularLocalRing (Localization.AtPrime q.asIdeal) := by
  rw [PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff]
  constructor
  · intro h p hp
    obtain ⟨_, ⟨f, rfl⟩, hpf, hf⟩ := h p hp
    exact ⟨f, hpf, fun q hq ↦ hf hq⟩
  · intro h p hp
    obtain ⟨f, hpf, hf⟩ := h p hp
    exact ⟨_, ⟨f, rfl⟩, hpf, fun q hq ↦ hf q hq⟩

/-- Every point of a regular ring belongs to its pointwise regular locus. -/
theorem primeRegularLocus_eq_univ (R : Type u) [CommRing R] [IsRegularRing R] :
    primeRegularLocus R = Set.univ := by
  ext p
  simp only [primeRegularLocus, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  infer_instance

/-- In particular the regular locus of a regular ring is open. -/
theorem isOpen_primeRegularLocus_of_isRegularRing
    (R : Type u) [CommRing R] [IsRegularRing R] : IsOpen (primeRegularLocus R) := by
  rw [primeRegularLocus_eq_univ]
  exact isOpen_univ

/-- Affine scheme stalks have exactly the regularity of the corresponding prime
localizations. -/
theorem isRegularLocalRing_stalk_Spec_iff
    (R : CommRingCat.{u}) (p : PrimeSpectrum R) :
    IsRegularLocalRing ((Spec R).presheaf.stalk p) ↔
      IsRegularLocalRing (Localization.AtPrime p.asIdeal) :=
  isRegularLocalRing_iff_of_ringEquiv (Spec.stalkIso R p).commRingCatIsoToRingEquiv

/-- The singular locus of `Spec R` is the complement of the affine regular locus. -/
theorem stalkSingularLocus_Spec_eq (R : CommRingCat.{u}) :
    stalkSingularLocus (Spec R) = (primeRegularLocus R)ᶜ := by
  ext p
  exact not_congr (isRegularLocalRing_stalk_Spec_iff R p)

/-- On an affine scheme, singular-locus closedness is precisely regular-locus
openness for the coordinate ring. -/
theorem isClosed_stalkSingularLocus_Spec_iff (R : CommRingCat.{u}) :
    IsClosed (stalkSingularLocus (Spec R)) ↔ IsOpen (primeRegularLocus R) := by
  rw [stalkSingularLocus_Spec_eq]
  exact isClosed_compl_iff

/-- Regularity of a stalk is unchanged by an open immersion. -/
theorem isRegularLocalRing_stalk_openImmersion_iff
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    IsRegularLocalRing (Y.presheaf.stalk (f x)) ↔
      IsRegularLocalRing (X.presheaf.stalk x) :=
  isRegularLocalRing_iff_of_ringEquiv
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv

/-- Singular loci restrict exactly along open immersions. -/
theorem preimage_stalkSingularLocus_openImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    f ⁻¹' stalkSingularLocus Y = stalkSingularLocus X := by
  ext x
  exact not_congr (isRegularLocalRing_stalk_openImmersion_iff f x)

/-- Pulling a scheme's singular locus back to any affine chart gives exactly the
complement of the corresponding ring's regular locus. -/
theorem preimage_stalkSingularLocus_fromSpec
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ⁻¹' stalkSingularLocus X = (primeRegularLocus Γ(X, U))ᶜ := by
  rw [preimage_stalkSingularLocus_openImmersion, stalkSingularLocus_Spec_eq]

set_option backward.isDefEq.respectTransparency false in
/-- Closedness of the actual singular locus is an affine-local property. This
equivalence isolates the globalization step from the missing algebraic theorem. -/
theorem isClosed_stalkSingularLocus_iff_affine (X : Scheme.{u}) :
    IsClosed (stalkSingularLocus X) ↔
      ∀ U : X.affineOpens, IsOpen (primeRegularLocus Γ(X, U)) := by
  constructor
  · intro h U
    have hc := h.preimage U.2.fromSpec.continuous
    rw [preimage_stalkSingularLocus_fromSpec U.2] at hc
    exact isClosed_compl_iff.mp hc
  · intro h
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    change IsAffineOpen U at hU
    let V : X.affineOpens := ⟨U, hU⟩
    have hpre : hU.fromSpec ⁻¹' (stalkSingularLocus X)ᶜ =
        primeRegularLocus Γ(X, U) := by
      rw [Set.preimage_compl, preimage_stalkSingularLocus_fromSpec, compl_compl]
    refine ⟨hU.fromSpec '' primeRegularLocus Γ(X, U), ?_,
      hU.fromSpec.isOpenEmbedding.isOpenMap _ (h V), ?_⟩
    · rw [← hpre]
      exact Set.image_preimage_subset _ _
    · refine ⟨hU.primeIdealOf ⟨x, hxU⟩, ?_, hU.fromSpec_primeIdealOf _⟩
      rw [← hpre]
      simpa only [Set.mem_preimage, hU.fromSpec_primeIdealOf] using hx

/-- An Artinian ring has discrete prime spectrum, so its regular locus is open,
without any reducedness assumption. -/
theorem isOpen_primeRegularLocus_of_isArtinianRing
    (R : Type u) [CommRing R] [IsArtinianRing R] :
    IsOpen (primeRegularLocus R) :=
  isOpen_discrete _

/-- The desired affine closedness theorem holds for every finite algebra over a
field, including nonreduced algebras. -/
theorem isClosed_stalkSingularLocus_Spec_of_moduleFinite
    (k : Type u) [Field k] (R : Type u) [CommRing R] [Algebra k R]
    [Module.Finite k R] : IsClosed (stalkSingularLocus (Spec (.of R))) := by
  let : IsArtinianRing R := IsArtinianRing.of_finite k R
  exact (isClosed_stalkSingularLocus_Spec_iff (.of R)).mpr
    (isOpen_primeRegularLocus_of_isArtinianRing R)

/-- Affine schemes with regular coordinate rings have no singular points. -/
theorem stalkSingularLocus_Spec_eq_empty
    (R : CommRingCat.{u}) [IsRegularRing R] :
    stalkSingularLocus (Spec R) = ∅ := by
  rw [stalkSingularLocus_Spec_eq, primeRegularLocus_eq_univ, Set.compl_univ]
  rfl

/-- Affine space over a field has empty pointwise singular locus. -/
theorem stalkSingularLocus_affineSpace_eq_empty
    (k : Type u) [Field k] (n : ℕ) :
    stalkSingularLocus (Spec (.of (MvPolynomial (Fin n) k))) = ∅ :=
  stalkSingularLocus_Spec_eq_empty _

end Pcf
