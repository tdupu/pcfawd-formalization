/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemePrimeToPSpecialization
public import Pcf.Bounding.AffineSchemeRamification
public import Pcf.Bounding.SchemePrimaryResidueMap
public import Pcf.Bounding.SchemeDeltaEtaleNoetherian

/-!
# Tameness at divisors of a self-map with prime-to-`p` monodromy

For a finite dominant self-map of a normal integral scheme of finite type over
a field of characteristic `p`, prime-to-`p` monodromy makes every divisorial
ramification index prime to `p` and every divisorial residue extension
separable. This is the codimension-one case of `latex/paper-p.tex`, Lemma
`lem:prime-to-p-restrict`, on actual scheme stalks. Consequently `δ = e`, and
the map is formally étale at a divisor whose index divides a power of `p`.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
  {X : Scheme.{u}} [IsIntegral X] [IsNormalScheme X] [IsLocallyNoetherian X]
  (s : X ⟶ Spec (.of k)) (h : X ⟶ X) [IsFinite h] [IsDominant h]

include hp k s in
/-- Sections over a nonempty open of a scheme over a characteristic-`p` field
have characteristic `p`. -/
theorem charP_sections_of_field (U : X.Opens) [Nonempty U] : CharP Γ(X, U) p := by
  let φ : k →+* Γ(X, U) := (s.appLE ⊤ U (fun _ _ => trivial)).hom.comp
    (Scheme.ΓSpecIso (.of k)).inv.hom
  exact charP_of_injective_ringHom (f := φ) φ.injective p

set_option backward.isDefEq.respectTransparency false in
include hp k s in
/-- **Tameness at a divisor on an affine chart.** -/
theorem schemeDivisor_isTamelyRamifiedAt_affine
    (hmono : IsPrimeToPMonodromyMap p h)
    (Q : SchemeDivisorPoint X) (U : X.affineOpens) (hx : h Q.1 ∈ (U : X.Opens)) :
    let V := finitePreimageAffine h U
    letI : Algebra Γ(X, U) Γ(X, V) := (h.app U).hom.toAlgebra
    Stacks.IsTamelyRamifiedAt Γ(X, U) Γ(X, V) (V.2.primeIdealOf ⟨Q.1, hx⟩) := by
  let V := finitePreimageAffine h U
  letI : Nonempty (U : X.Opens) := ⟨⟨_, hx⟩⟩
  letI : Nonempty (V : X.Opens) := ⟨⟨Q.1, hx⟩⟩
  have hgp : h (genericPoint X) = genericPoint X := map_genericPoint_eq_of_isDominant h
  have hmem : h (genericPoint X) ∈ (U : X.Opens) := by
    rw [hgp]
    exact ((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr
      (by simpa using ‹Nonempty (U : X.Opens)›)
  let R := Γ(X, U)
  let S := Γ(X, V)
  let F := X.presheaf.stalk (h (genericPoint X))
  let E := X.functionField
  letI : Algebra R S := (h.app U).hom.toAlgebra
  letI : Module.Finite R S := moduleFinite_finitePreimageAffine h U
  letI : FaithfulSMul R S := faithfulSMul_finitePreimageAffine h U
  letI : IsIntegrallyClosed R := IsNormalScheme.component_integrallyClosed U
  letI : IsIntegrallyClosed S := IsNormalScheme.component_integrallyClosed V
  letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian U
  letI : CharP R p := charP_sections_of_field p hp k s (U : X.Opens)
  let e := (X.presheaf.stalkCongr (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  have hfield : IsField F := e.toMulEquiv.isField (Field.toIsField _)
  letI : Field F := hfield.toField
  letI : Algebra R F := (X.presheaf.germ U (h (genericPoint X)) hmem).hom.toAlgebra
  letI : IsFractionRing R F := isFractionRing_targetGenericStalk_of_finiteDominant h U
  letI : IsFractionRing S E := functionField_isFractionRing_of_isAffineOpen X V V.2
  letI : Algebra R E := ((X.germToFunctionField V).hom.comp (h.app U).hom).toAlgebra
  letI : IsScalarTower R S E := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra F E := (h.stalkMap (genericPoint X)).hom.toAlgebra
  letI : IsScalarTower R F E := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact (h.germ_stalkMap_apply U (genericPoint X) hmem r).symm)
  let P := (U.2.primeIdealOf ⟨h Q.1, hx⟩).asIdeal
  have hunder : (V.2.primeIdealOf ⟨Q.1, hx⟩).asIdeal.under R = P := by
    have hc := congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE (U : X.Opens) U.2 (V : X.Opens) V.2 le_rfl hx)
    simp only [PrimeSpectrum.comap_asIdeal] at hc
    change Ideal.comap (h.app U).hom _ = P
    rw [← Scheme.Hom.appLE_eq_app]
    exact hc
  have hP : P.height = 1 := by
    have h1 := pointClosureIdealSheaf_ideal_height (Q.mapFiniteDominantNormal h) U hx
    have h2 := pointClosureIdealSheaf_ideal (Q.mapFiniteDominantNormal h).1 U hx
    rw [h2] at h1
    exact h1
  exact finiteNormalCover_isTamelyRamifiedAt_of_heightOne p hp R S F E hmono P hP
    (V.2.primeIdealOf ⟨Q.1, hx⟩) hunder

set_option backward.isDefEq.respectTransparency false in
/-- The residue-field algebra of a tame prime is the residue-field map of the
ring map. -/
theorem residueField_algebraMap_eq_map {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (q : Ideal S) [q.IsPrime] :
    letI : Algebra (Localization.AtPrime (q.under R)) (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver (q.under R) q
    algebraMap (q.under R).ResidueField q.ResidueField =
      Ideal.ResidueField.map (q.under R) q (algebraMap R S) rfl := by
  letI : Algebra (Localization.AtPrime (q.under R)) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver (q.under R) q
  apply Ideal.ResidueField.ringHom_ext
  ext a
  simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
  rw [← IsScalarTower.algebraMap_apply R (q.under R).ResidueField q.ResidueField,
    IsScalarTower.algebraMap_apply R S q.ResidueField]

/-- Separability of a residue extension along equal ring maps and equal
contracted primes. -/
theorem residueField_isSeparable_transport {R S : Type*} [CommRing R] [CommRing S]
    (q : Ideal S) [q.IsPrime] (φ ψ : R →+* S) (hψ : ψ = φ)
    (P1 : Ideal R) [P1.IsPrime] (hc : P1 = q.comap ψ)
    (hsep : @Algebra.IsSeparable (q.comap φ).ResidueField q.ResidueField _ _
      (Ideal.ResidueField.map (q.comap φ) q φ rfl).toAlgebra) :
    @Algebra.IsSeparable P1.ResidueField q.ResidueField _ _
      (Ideal.ResidueField.map P1 q ψ hc).toAlgebra := by
  subst hψ
  subst hc
  exact hsep

set_option backward.isDefEq.respectTransparency false in
/-- The tame residue separability, phrased with the residue map. -/
theorem residueField_isSeparable_map_of_tame {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (q : Ideal S) [q.IsPrime]
    (hsep : letI : Algebra (Localization.AtPrime (q.under R)) (Localization.AtPrime q) :=
        Localization.AtPrime.algebraOfLiesOver (q.under R) q
      Algebra.IsSeparable (q.under R).ResidueField q.ResidueField) :
    @Algebra.IsSeparable (q.comap (algebraMap R S)).ResidueField q.ResidueField _ _
      (Ideal.ResidueField.map (q.comap (algebraMap R S)) q (algebraMap R S) rfl).toAlgebra := by
  letI : Algebra (Localization.AtPrime (q.under R)) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver (q.under R) q
  have hmap := residueField_algebraMap_eq_map (R := R) q
  exact @Algebra.IsSeparable.of_equiv_equiv _ _ _ _ _ _ _ _ _
    (Ideal.ResidueField.map (q.comap (algebraMap R S)) q (algebraMap R S) rfl).toAlgebra
    (RingEquiv.refl _) (RingEquiv.refl _) (by
      rw [RingHom.algebraMap_toAlgebra, ← hmap]
      rfl) hsep

set_option backward.isDefEq.respectTransparency false in
include hp k s in
/-- **Tameness at every divisor.** A finite dominant self-map with
prime-to-`p` monodromy has divisorial ramification indices prime to `p` and
separable divisorial residue extensions. -/
theorem schemeDivisor_tame_of_primeToP
    (hmono : IsPrimeToPMonodromyMap p h) (Q : SchemeDivisorPoint X) :
    ¬ p ∣ schemeDivisorRamificationIdx h Q ∧
      (letI := (h.residueFieldMap Q.1).hom.toAlgebra
       Algebra.IsSeparable (X.residueField (h Q.1)) (X.residueField Q.1)) := by
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset
    (show h Q.1 ∈ (⊤ : X.Opens) from trivial)
  let U : X.affineOpens := ⟨W, hW⟩
  have hx : h Q.1 ∈ (U : X.Opens) := hxW
  letI : Nonempty (U : X.Opens) := ⟨⟨_, hx⟩⟩
  let V := finitePreimageAffine h U
  let R := Γ(X, U)
  let S := Γ(X, V)
  letI : Algebra R S := (h.app U).hom.toAlgebra
  letI : CharP R p := charP_sections_of_field p hp k s (U : X.Opens)
  have htame := schemeDivisor_isTamelyRamifiedAt_affine p hp k s h hmono Q U hx
  let q := V.2.primeIdealOf ⟨Q.1, hx⟩
  let P0 := q.asIdeal.under R
  letI : CharP P0.ResidueField p :=
    CharP.of_ringHom_of_ne_zero (algebraMap R P0.ResidueField) p hp.ne_zero
  constructor
  · have he : schemeDivisorRamificationIdx h Q = q.asIdeal.ramificationIdx R := by
      have h1 := schemeDivisorRamificationIdx_eq_heightOneRamificationIdx h U
        (affinePrimeOfSchemeDivisorPoint Q V hx)
      rw [schemeDivisorPointOfAffinePrime_affinePrime] at h1
      rw [h1]
      change Ideal.ramificationIdx _ _ = _
      rw [affinePrimeOfSchemeDivisorPoint_asIdeal, pointClosureIdealSheaf_ideal Q.1 V hx]
    rw [he]
    exact (CharP.isUnit_natCast_iff hp).mp htame.1
  · let φ' := (h.appLE U V le_rfl).hom
    have hφ : φ' = algebraMap R S := by
      change (h.appLE U (h ⁻¹ᵁ (U : X.Opens)) le_rfl).hom = (h.app U).hom
      rw [Scheme.Hom.appLE_eq_app]
    have hsep0 := htame.2
    have hsepA : @Algebra.IsSeparable (q.asIdeal.comap (algebraMap R S)).ResidueField
        q.asIdeal.ResidueField _ _
        (Ideal.ResidueField.map (q.asIdeal.comap (algebraMap R S)) q.asIdeal
          (algebraMap R S) rfl).toAlgebra :=
      residueField_isSeparable_map_of_tame q.asIdeal hsep0
    have hnat := schemeAffineResidueFieldEquiv_naturality_of_finite h U Q.1 hx
    let p' := (U.2.primeIdealOf ⟨h Q.1, hx⟩).asIdeal
    have hcontract : p' = q.asIdeal.comap φ' := by
      simpa only [PrimeSpectrum.comap_asIdeal] using (congrArg PrimeSpectrum.asIdeal
        (IsAffineOpen.comap_primeIdealOf_appLE (U : X.Opens) U.2
          (V : X.Opens) V.2 le_rfl hx)).symm
    have hsep1 := residueField_isSeparable_transport q.asIdeal (algebraMap R S) φ' hφ
      p' hcontract hsepA
    exact @Algebra.IsSeparable.of_equiv_equiv _ _ _ _ _ _ _ _
      (Ideal.ResidueField.map p' q.asIdeal φ' hcontract).toAlgebra
      (h.residueFieldMap Q.1).hom.toAlgebra
      (schemeAffineResidueFieldEquiv X U U.2 (h Q.1) hx)
      (schemeAffineResidueFieldEquiv X V V.2 Q.1 hx) hnat hsep1

include hp k s in
/-- With prime-to-`p` monodromy the weighted divisorial degree is the
ramification index. -/
theorem schemeDivisorDelta_eq_ramificationIdx_of_primeToP
    (hmono : IsPrimeToPMonodromyMap p h) (Q : SchemeDivisorPoint X) :
    schemeDivisorDelta h Q = schemeDivisorRamificationIdx h Q := by
  have hsep := (schemeDivisor_tame_of_primeToP p hp k s h hmono Q).2
  letI := (h.residueFieldMap Q.1).hom.toAlgebra
  unfold schemeDivisorDelta
  rw [Algebra.IsSeparable.finInsepDegree_eq, mul_one]

include hp k s in
/-- With prime-to-`p` monodromy, a divisorial ramification index dividing a
power of `p` is one and the map is formally étale at that divisor. -/
theorem formallyEtale_of_ramificationIdx_dvd_pow_of_primeToP
    (hmono : IsPrimeToPMonodromyMap p h) (Q : SchemeDivisorPoint X) (b : ℕ)
    (hdvd : schemeDivisorRamificationIdx h Q ∣ p ^ b) :
    (h.stalkMap Q.1).hom.FormallyEtale := by
  have hnd := (schemeDivisor_tame_of_primeToP p hp k s h hmono Q).1
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hc0 : c = 0 := by
    by_contra hne
    exact hnd (hc ▸ dvd_pow_self p hne)
  rw [← schemeDivisorDelta_eq_one_iff_formallyEtale,
    schemeDivisorDelta_eq_ramificationIdx_of_primeToP p hp k s h hmono Q, hc, hc0, pow_zero]

#print axioms charP_sections_of_field
#print axioms schemeDivisor_isTamelyRamifiedAt_affine
#print axioms residueField_algebraMap_eq_map
#print axioms schemeDivisor_tame_of_primeToP
#print axioms schemeDivisorDelta_eq_ramificationIdx_of_primeToP
#print axioms formallyEtale_of_ramificationIdx_dvd_pow_of_primeToP

end
end Pcf
