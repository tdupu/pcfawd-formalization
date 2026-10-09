/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Bounding.SmoothRegularLocal
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Local

/-!
# Cotangent prerequisite for finite-type singular-locus closedness

This module proves the left-exact cotangent step in the regular-to-smooth
implication over a perfect field: for an essentially finite-type local
`k`-algebra `R`, the map
`m / m² → κ ⊗[R] Ω[R/k]` has a linear retraction. The proof lifts the identity
of the formally smooth residue field through the square-zero thickening
`R / m²`. It also proves the resulting dimension formula and rewrites the
local Jacobian criterion as one conormal-dimension inequality. Neither
regularity nor closedness of a locus is assumed.

The general theorem `IsClosed (stalkSingularLocus X)` for a scheme locally of
finite type over a characteristic-zero field remains unproved. Its remaining
algebraic obligation is: if `S` is a finite-type algebra over a perfect field
`k` and `p` is prime, then regularity of `Localization.AtPrime p` implies
`Algebra.IsSmoothAt k p`. Together with `SmoothRegularLocal`, this identifies
the regular locus with the open smooth locus. The cotangent retraction proved
here supplies the left-exactness used in Stacks Project Tags `00TU` and `00TV`.

More precisely, `formallySmooth_iff_conormal_finrank_bound_of_perfectField`
reduces the remaining step, for a local polynomial presentation `P → R` with
kernel `I` and common residue field `κ`, to
`dimκ (κ ⊗[R] I/I²) + dim R ≤ dim P` when `R` is regular. This is the upper
bound on the number of generators of a regular quotient's defining ideal
(Stacks Project Tag `00NR`). The available Krull height theorem gives the
opposite inequality, so it cannot discharge this step. No such bound or
regular-to-smooth implication is added as an assumption or axiom here.
-/

universe u v w

open IsLocalRing KaehlerDifferential TensorProduct

namespace Pcf

/-- A surjection onto a formally smooth algebra has a split-injective
conormal-to-differentials map. The source algebra need not be smooth. -/
theorem exists_retraction_kerCotangentToTensor_of_formallySmooth
    (k : Type u) (R : Type v) (S : Type w)
    [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
    [Algebra.FormallySmooth k S]
    (hsurj : Function.Surjective (algebraMap R S)) :
    ∃ l, l ∘ₗ kerCotangentToTensor k R S = LinearMap.id := by
  let f := IsScalarTower.toAlgHom k R S
  have hsurj' : Function.Surjective f.kerSquareLift :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ hsurj
  have hnil : IsNilpotent (RingHom.ker f.kerSquareLift.toRingHom) := by
    refine ⟨2, ?_⟩
    rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
    rfl
  let g := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k S)
    f.kerSquareLift hsurj' hnil
  have hg : f.kerSquareLift.comp g = AlgHom.id k S :=
    Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _
  obtain ⟨l, hl⟩ := (retractionKerCotangentToTensorEquivSection (R := k) hsurj).symm
    ⟨g, hg⟩
  exact ⟨l, hl⟩

#print axioms exists_retraction_kerCotangentToTensor_of_formallySmooth

/-- Over a perfect field, the cotangent sequence of an essentially finite-type
local algebra is split injective at the conormal term of its residue field. -/
theorem exists_retraction_residueField_kerCotangentToTensor_of_perfectField
    (k : Type u) (R : Type v) [Field k] [PerfectField k]
    [CommRing R] [IsLocalRing R] [Algebra k R] [Algebra.EssFiniteType k R] :
    ∃ l, l ∘ₗ kerCotangentToTensor k R (ResidueField R) = LinearMap.id := by
  have : Algebra.EssFiniteType k (ResidueField R) :=
    Algebra.EssFiniteType.comp k R (ResidueField R)
  exact exists_retraction_kerCotangentToTensor_of_formallySmooth k R (ResidueField R)
    IsLocalRing.residue_surjective

#print axioms exists_retraction_residueField_kerCotangentToTensor_of_perfectField

/-- The left map of the residue-field cotangent sequence is injective over a
perfect field, with no regularity assumption on the local algebra. -/
theorem injective_residueField_kerCotangentToTensor_of_perfectField
    (k : Type u) (R : Type v) [Field k] [PerfectField k]
    [CommRing R] [IsLocalRing R] [Algebra k R] [Algebra.EssFiniteType k R] :
    Function.Injective (kerCotangentToTensor k R (ResidueField R)) := by
  obtain ⟨l, hl⟩ :=
    exists_retraction_residueField_kerCotangentToTensor_of_perfectField k R
  exact Function.LeftInverse.injective (fun x ↦ LinearMap.congr_fun hl x)

#print axioms injective_residueField_kerCotangentToTensor_of_perfectField

/-- The dimension formula for differentials at an essentially finite-type
local algebra over a perfect field. This separates the embedding dimension
from the contribution of the residue-field extension. -/
theorem finrank_residueField_tensor_kaehlerDifferential_of_perfectField
    (k : Type u) (R : Type v) [Field k] [PerfectField k]
    [CommRing R] [IsLocalRing R] [Algebra k R] [Algebra.EssFiniteType k R] :
    Module.finrank (ResidueField R) ((ResidueField R) ⊗[R] Ω[R⁄k]) =
      Module.finrank (ResidueField R) (CotangentSpace R) +
        Module.finrank (ResidueField R) Ω[(ResidueField R)⁄k] := by
  let e : CotangentSpace R ≃ₗ[R]
      (RingHom.ker (algebraMap R (ResidueField R))).Cotangent :=
    Ideal.Cotangent.equivOfEq _ _ (by rw [ResidueField.algebraMap_eq, ker_residue])
  let c : CotangentSpace R →ₗ[ResidueField R] (ResidueField R) ⊗[R] Ω[R⁄k] :=
    LinearMap.extendScalarsOfSurjective residue_surjective
      ((kerCotangentToTensor k R (ResidueField R)).comp e.toLinearMap)
  let d := KaehlerDifferential.mapBaseChange k R (ResidueField R)
  have hc : Function.Injective c :=
    (injective_residueField_kerCotangentToTensor_of_perfectField k R).comp e.injective
  have hcd : LinearMap.range c = LinearMap.ker d := by
    ext x
    change (∃ y, kerCotangentToTensor k R (ResidueField R) (e y) = x) ↔ d x = 0
    rw [(exact_kerCotangentToTensor_mapBaseChange k R (ResidueField R)
      residue_surjective) x]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨e y, hy⟩
    · rintro ⟨y, hy⟩
      obtain ⟨z, rfl⟩ := e.surjective y
      exact ⟨z, hy⟩
  have hd : Function.Surjective d :=
    KaehlerDifferential.mapBaseChange_surjective k R (ResidueField R) residue_surjective
  have hdim := d.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hd, finrank_top, ← hcd,
    LinearMap.finrank_range_of_inj hc] at hdim
  exact hdim.symm.trans (Nat.add_comm _ _)

#print axioms finrank_residueField_tensor_kaehlerDifferential_of_perfectField

/-- The cotangent-dimension formula at every prime of a finite-type algebra
over a characteristic-zero field. No smoothness or regularity is assumed. -/
theorem finrank_residueField_tensor_kaehlerDifferential_atPrime_of_charZero
    (k : Type u) (S : Type v) [Field k] [CharZero k]
    [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (p : Ideal S) [p.IsPrime] :
    Module.finrank (ResidueField (Localization.AtPrime p))
        ((ResidueField (Localization.AtPrime p)) ⊗[Localization.AtPrime p]
          Ω[(Localization.AtPrime p)⁄k]) =
      Module.finrank (ResidueField (Localization.AtPrime p))
          (CotangentSpace (Localization.AtPrime p)) +
        Module.finrank (ResidueField (Localization.AtPrime p))
          Ω[(ResidueField (Localization.AtPrime p))⁄k] :=
  finrank_residueField_tensor_kaehlerDifferential_of_perfectField k (Localization.AtPrime p)

#print axioms finrank_residueField_tensor_kaehlerDifferential_atPrime_of_charZero

/-- The local Jacobian criterion, expressed as the single numerical inequality
remaining after the cotangent-dimension formula. The presentation algebra is
formally smooth with finite free differentials; regularity of the quotient is
not an assumption. -/
theorem formallySmooth_iff_conormal_finrank_bound_of_perfectField
    (k : Type u) (R : Type v) [Field k] [PerfectField k]
    [CommRing R] [IsLocalRing R] [Algebra k R] [Algebra.EssFiniteType k R]
    (P : Algebra.Extension.{w} k R) [Algebra.FormallySmooth k P.Ring]
    [Module.Free P.Ring Ω[P.Ring⁄k]] [Module.Finite P.Ring Ω[P.Ring⁄k]]
    (hI : P.ker.FG) :
    Algebra.FormallySmooth k R ↔
      Module.finrank (ResidueField R) ((ResidueField R) ⊗[R] P.Cotangent) +
          Module.finrank (ResidueField R) (CotangentSpace R) +
          Module.finrank (ResidueField R) Ω[(ResidueField R)⁄k] ≤
        Module.finrank (ResidueField R) ((ResidueField R) ⊗[R] P.CotangentSpace) := by
  have : Module.Finite R P.Cotangent := Algebra.Extension.Cotangent.finite hI
  let c := P.cotangentComplex.baseChange (ResidueField R)
  let d := P.toKaehler.baseChange (ResidueField R)
  have hcd : LinearMap.ker d = LinearMap.range c := by
    apply LinearMap.exact_iff.mp
    exact lTensor_exact (ResidueField R) P.exact_cotangentComplex_toKaehler
      P.toKaehler_surjective
  have hd : Function.Surjective d :=
    LinearMap.lTensor_surjective (ResidueField R) P.toKaehler_surjective
  have hdim := d.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hd, finrank_top, hcd,
    finrank_residueField_tensor_kaehlerDifferential_of_perfectField k R] at hdim
  rw [Algebra.FormallySmooth.iff_injective_lTensor_residueField P hI]
  change Function.Injective c ↔ _
  rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  have hdim' := c.finrank_range_add_finrank_ker
  omega

#print axioms formallySmooth_iff_conormal_finrank_bound_of_perfectField

end Pcf
