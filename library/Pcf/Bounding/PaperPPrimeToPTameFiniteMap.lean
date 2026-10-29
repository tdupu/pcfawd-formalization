/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemePrimeToPTameDivisor

/-!
# Prime-to-`p` tameness for a finite map between two normal schemes

`SchemePrimeToPTameDivisor` proves divisorial tameness for self-maps. The
restriction maps in `paper-p.tex`, Theorem `thm:tower-restrict`, have
different source and target, so the same affine specialization is needed
for an actual finite dominant morphism `X ⟶ Y`.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory

universe u
noncomputable section

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-- Tameness at a source divisor for an actual finite dominant map of
normal schemes with prime-to-`p` generic monodromy. -/
theorem finiteMap_schemeDivisor_isTamelyRamifiedAt_affine
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (s : Y ⟶ Spec (.of k)) (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (hmono : IsPrimeToPMonodromyMap p f)
    (Q : SchemeDivisorPoint X) (U : Y.affineOpens)
    (hx : f Q.1 ∈ (U : Y.Opens)) :
    let V := finitePreimageAffine f U
    letI : Algebra Γ(Y, U) Γ(X, V) := (f.app U).hom.toAlgebra
    Stacks.IsTamelyRamifiedAt Γ(Y, U) Γ(X, V)
      (V.2.primeIdealOf ⟨Q.1, hx⟩) := by
  let V := finitePreimageAffine f U
  letI : Nonempty (U : Y.Opens) := ⟨⟨_, hx⟩⟩
  letI : Nonempty (V : X.Opens) := ⟨⟨Q.1, hx⟩⟩
  have hgp : f (genericPoint X) = genericPoint Y :=
    map_genericPoint_eq_of_isDominant f
  have hmem : f (genericPoint X) ∈ (U : Y.Opens) := by
    rw [hgp]
    exact ((genericPoint_spec Y).mem_open_set_iff U.1.isOpen).mpr
      (by simpa using ‹Nonempty (U : Y.Opens)›)
  let R := Γ(Y, U)
  let S := Γ(X, V)
  let F := Y.presheaf.stalk (f (genericPoint X))
  let E := X.functionField
  letI : Algebra R S := (f.app U).hom.toAlgebra
  letI : Module.Finite R S := moduleFinite_finitePreimageAffine f U
  letI : FaithfulSMul R S := faithfulSMul_finitePreimageAffine f U
  letI : IsIntegrallyClosed R := IsNormalScheme.component_integrallyClosed U
  letI : IsIntegrallyClosed S := IsNormalScheme.component_integrallyClosed V
  letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian U
  letI : CharP R p := charP_sections_of_field p hp k s (U : Y.Opens)
  let e := (Y.presheaf.stalkCongr (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  have hfield : IsField F := e.toMulEquiv.isField (Field.toIsField _)
  letI : Field F := hfield.toField
  letI : Algebra R F := (Y.presheaf.germ U (f (genericPoint X)) hmem).hom.toAlgebra
  letI : IsFractionRing R F := isFractionRing_targetGenericStalk_of_finiteDominant f U
  letI : IsFractionRing S E := functionField_isFractionRing_of_isAffineOpen X V V.2
  letI : Algebra R E := ((X.germToFunctionField V).hom.comp (f.app U).hom).toAlgebra
  letI : IsScalarTower R S E := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra F E := (f.stalkMap (genericPoint X)).hom.toAlgebra
  letI : IsScalarTower R F E := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact (f.germ_stalkMap_apply U (genericPoint X) hmem r).symm)
  let P := (U.2.primeIdealOf ⟨f Q.1, hx⟩).asIdeal
  have hunder : (V.2.primeIdealOf ⟨Q.1, hx⟩).asIdeal.under R = P := by
    have hc := congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE (U : Y.Opens) U.2
        (V : X.Opens) V.2 le_rfl hx)
    simp only [PrimeSpectrum.comap_asIdeal] at hc
    change Ideal.comap (f.app U).hom _ = P
    rw [← Scheme.Hom.appLE_eq_app]
    exact hc
  have hP : P.height = 1 := by
    have h1 := pointClosureIdealSheaf_ideal_height (Q.mapFiniteDominantNormal f) U hx
    have h2 := pointClosureIdealSheaf_ideal (Q.mapFiniteDominantNormal f).1 U hx
    rw [h2] at h1
    exact h1
  exact finiteNormalCover_isTamelyRamifiedAt_of_heightOne p hp R S F E hmono
    P hP (V.2.primeIdealOf ⟨Q.1, hx⟩) hunder

/-- The codimension-one case of `lem:prime-to-p-restrict` for an actual
finite dominant map between possibly different normal varieties: the
ramification index is prime to `p` and the residue extension is separable. -/
theorem finiteMap_schemeDivisor_tame_of_primeToP
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (s : Y ⟶ Spec (.of k)) (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (hmono : IsPrimeToPMonodromyMap p f) (Q : SchemeDivisorPoint X) :
    ¬ p ∣ schemeDivisorRamificationIdx f Q ∧
      (letI := (f.residueFieldMap Q.1).hom.toAlgebra
       Algebra.IsSeparable (Y.residueField (f Q.1)) (X.residueField Q.1)) := by
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset
    (show f Q.1 ∈ (⊤ : Y.Opens) from trivial)
  let U : Y.affineOpens := ⟨W, hW⟩
  have hx : f Q.1 ∈ (U : Y.Opens) := hxW
  letI : Nonempty (U : Y.Opens) := ⟨⟨_, hx⟩⟩
  let V := finitePreimageAffine f U
  let R := Γ(Y, U)
  let S := Γ(X, V)
  letI : Algebra R S := (f.app U).hom.toAlgebra
  letI : CharP R p := charP_sections_of_field p hp k s (U : Y.Opens)
  have htame := finiteMap_schemeDivisor_isTamelyRamifiedAt_affine
    p hp k s f hmono Q U hx
  let q := V.2.primeIdealOf ⟨Q.1, hx⟩
  let P0 := q.asIdeal.under R
  letI : CharP P0.ResidueField p :=
    CharP.of_ringHom_of_ne_zero (algebraMap R P0.ResidueField) p hp.ne_zero
  constructor
  · have he : schemeDivisorRamificationIdx f Q = q.asIdeal.ramificationIdx R := by
      have h1 := schemeDivisorRamificationIdx_eq_heightOneRamificationIdx f U
        (affinePrimeOfSchemeDivisorPoint Q V hx)
      rw [schemeDivisorPointOfAffinePrime_affinePrime] at h1
      rw [h1]
      change Ideal.ramificationIdx _ _ = _
      rw [affinePrimeOfSchemeDivisorPoint_asIdeal,
        pointClosureIdealSheaf_ideal Q.1 V hx]
    rw [he]
    exact (CharP.isUnit_natCast_iff hp).mp htame.1
  · let φ' := (f.appLE U V le_rfl).hom
    have hφ : φ' = algebraMap R S := by
      change (f.appLE U (f ⁻¹ᵁ (U : Y.Opens)) le_rfl).hom = (f.app U).hom
      rw [Scheme.Hom.appLE_eq_app]
    have hsep0 := htame.2
    have hsepA : @Algebra.IsSeparable (q.asIdeal.comap (algebraMap R S)).ResidueField
        q.asIdeal.ResidueField _ _
        (Ideal.ResidueField.map (q.asIdeal.comap (algebraMap R S)) q.asIdeal
          (algebraMap R S) rfl).toAlgebra :=
      residueField_isSeparable_map_of_tame q.asIdeal hsep0
    have hnat := schemeAffineResidueFieldEquiv_naturality_of_finite f U Q.1 hx
    let p' := (U.2.primeIdealOf ⟨f Q.1, hx⟩).asIdeal
    have hcontract : p' = q.asIdeal.comap φ' := by
      simpa only [PrimeSpectrum.comap_asIdeal] using (congrArg PrimeSpectrum.asIdeal
        (IsAffineOpen.comap_primeIdealOf_appLE (U : Y.Opens) U.2
          (V : X.Opens) V.2 le_rfl hx)).symm
    have hsep1 := residueField_isSeparable_transport q.asIdeal
      (algebraMap R S) φ' hφ p' hcontract hsepA
    exact @Algebra.IsSeparable.of_equiv_equiv _ _ _ _ _ _ _ _
      (Ideal.ResidueField.map p' q.asIdeal φ' hcontract).toAlgebra
      (f.residueFieldMap Q.1).hom.toAlgebra
      (schemeAffineResidueFieldEquiv Y U U.2 (f Q.1) hx)
      (schemeAffineResidueFieldEquiv X V V.2 Q.1 hx) hnat hsep1

/-- For a general prime-to-`p` finite normal cover, the manuscript's
weighted divisorial degree is its ordinary ramification index. -/
theorem finiteMap_schemeDivisorDelta_eq_ramificationIdx_of_primeToP
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (s : Y ⟶ Spec (.of k)) (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (hmono : IsPrimeToPMonodromyMap p f) (Q : SchemeDivisorPoint X) :
    schemeDivisorDelta f Q = schemeDivisorRamificationIdx f Q := by
  have hsep := (finiteMap_schemeDivisor_tame_of_primeToP p hp k s f hmono Q).2
  letI := (f.residueFieldMap Q.1).hom.toAlgebra
  unfold schemeDivisorDelta
  rw [Algebra.IsSeparable.finInsepDegree_eq, mul_one]

/-- A divisorial index dividing a `p`-power is one and the map is
formally étale for any finite dominant normal cover with prime-to-`p`
monodromy, not just for self-maps. -/
theorem finiteMap_formallyEtale_of_ramificationIdx_dvd_pow_of_primeToP
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (s : Y ⟶ Spec (.of k)) (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (hmono : IsPrimeToPMonodromyMap p f) (Q : SchemeDivisorPoint X) (b : ℕ)
    (hdvd : schemeDivisorRamificationIdx f Q ∣ p ^ b) :
    (f.stalkMap Q.1).hom.FormallyEtale := by
  have hnd := (finiteMap_schemeDivisor_tame_of_primeToP p hp k s f hmono Q).1
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hc0 : c = 0 := by
    by_contra hne
    exact hnd (hc ▸ dvd_pow_self p hne)
  rw [← schemeDivisorDelta_eq_one_iff_formallyEtale,
    finiteMap_schemeDivisorDelta_eq_ramificationIdx_of_primeToP p hp k s f hmono Q,
    hc, hc0, pow_zero]

#print axioms finiteMap_schemeDivisor_isTamelyRamifiedAt_affine
#print axioms finiteMap_schemeDivisor_tame_of_primeToP
#print axioms finiteMap_schemeDivisorDelta_eq_ramificationIdx_of_primeToP
#print axioms finiteMap_formallyEtale_of_ramificationIdx_dvd_pow_of_primeToP

end
end Pcf
