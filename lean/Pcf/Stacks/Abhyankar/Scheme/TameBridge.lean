/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.Scheme.ChartData

/-!
# Tame ramification in codimension one on an affine chart

The definition of "`Y` is tamely ramified over `X` in codimension one" (Stacks Section 58.31,
Tag `0BSE`; pcf `IsTamelyRamifiedInCodimOne`) is stated intrinsically: for every point `ξ ∉ U`
with `dim 𝒪_{X,ξ} = 1`, the `K_ξ`-algebra `L_ξ = Γ(Y ×_X Spec K_ξ)` is tamely ramified with
respect to `𝒪_{X,ξ}` (Tag `09E9`).  This file identifies that condition on an affine chart
`V = Spec R` on which `D` is cut out by `a`, where `Y` restricts to `Spec M`:

* for `𝔭 ∋ a` with `dim R_𝔭 = 1` the point `ξ = 𝔭 ∈ V` lies in `D`, `𝒪_{X,ξ} ≅ R_𝔭`
  (`IsAffineOpen.isLocalization_stalk`), and `Spec K_ξ → X` factors as
  `Spec K_ξ → Spec R ≅ V ⊂ X`;
* hence `Y ×_X Spec K_ξ ≅ Spec(K_ξ ⊗_R M)` (`isPullback_tensor_fromSpec`) and
  `L_ξ ≅ K_ξ ⊗_R M ≅ Frac(R_𝔭) ⊗_R M` compatibly with the structure maps;
* tame ramification is invariant under compatible ring isomorphisms
  (`IsTamelyRamifiedOver.of_ringEquiv`, `IsTamelyRamifiedAt.of_ringEquiv`, via
  `ramificationIdx_eq_of_ringEquiv` for Mathlib's length-defined `Ideal.ramificationIdx` and
  `Algebra.IsSeparable.of_equiv_equiv` for residue fields).

The output `chartTame_of_isTamelyRamifiedInCodimOne` is the chart form `ChartTame a M` used by the
affine statement.  Stacks treats this identification as evident ("as in the discussion above")
in the proof of Tag `0EYG`; the transport lemmas are general API for `IsTamelyRamifiedOver`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TensorProduct

namespace Pcf.Stacks.SchemeLevel

universe u v w
/-- The length of `A ⧸ I` over `A` is invariant under a ring isomorphism `A ≃+* A'`. -/
theorem length_quotient_map_ringEquiv {A A' : Type*} [CommRing A] [CommRing A'] (φ : A ≃+* A')
    (I : Ideal A) : Module.length A (A ⧸ I) = Module.length A' (A' ⧸ I.map φ) := by
  let ψ : A ⧸ I ≃+* A' ⧸ I.map φ := Ideal.quotientEquiv I (I.map φ) φ rfl
  rw [Module.length_eq_of_surjective (R := A ⧸ I) Ideal.Quotient.mk_surjective,
    Module.length_eq_of_surjective (R := A' ⧸ I.map φ) (S := A') Ideal.Quotient.mk_surjective]
  let _ : Algebra (A ⧸ I) (A' ⧸ I.map φ) := ψ.toRingHom.toAlgebra
  rw [(AlgEquiv.ofRingEquiv (f := ψ) (fun _ ↦ rfl)).toLinearEquiv.length_eq,
    Module.length_eq_of_surjective (S := A ⧸ I) (R := A' ⧸ I.map φ) ψ.surjective]

/-- A natural number is invertible in `κ(𝔭)` iff it does not lie in `𝔭`. -/
theorem natCast_isUnit_residueField_iff {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
    (n : ℕ) : IsUnit ((n : p.ResidueField)) ↔ (n : R) ∉ p := by
  rw [isUnit_iff_ne_zero, ← map_natCast (algebraMap R p.ResidueField), ne_eq,
    Ideal.algebraMap_residueField_eq_zero]

/-- The residue field map `κ(q ∩ R) → κ(q)` is compatible with `R → S`. -/
theorem residueField_algebraMap_algebraMap {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S]
    (q : Ideal S) [q.IsPrime] (x : R) :
    letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q
    algebraMap (q.under R).ResidueField q.ResidueField (algebraMap R _ x) =
      algebraMap S q.ResidueField (algebraMap R S x) := by
  let _ := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime (q.under R)),
    IsScalarTower.algebraMap_apply S (Localization.AtPrime q) q.ResidueField]
  erw [IsLocalRing.ResidueField.algebraMap_residue]
  congr 1
  exact Localization.localRingHom_to_map _ _ _ _ _

/-- `Ideal.residueFieldRingEquiv` is compatible with the structure maps. -/
theorem residueField_map_localRingEquiv_algebraMap {A B : Type*} [CommRing A] [CommRing B]
    (J : Ideal A) (K : Ideal B) [J.IsPrime] [K.IsPrime] (e : A ≃+* B) (h : J = K.comap e)
    (x : A) :
    Ideal.residueFieldRingEquiv J K e h (algebraMap A _ x) = algebraMap B _ (e x) :=
  Ideal.ResidueField.map_algebraMap J K (e : A →+* B) h x

section
variable {R : Type u} {S : Type v} {R' : Type w} {S' : Type*} [CommRing R] [CommRing S]
  [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R' S']
  (e1 : R ≃+* R') (e2 : S ≃+* S') (h : ∀ x, e2 (algebraMap R S x) = algebraMap R' S' (e1 x))

include h in
/-- Contractions correspond under compatible ring isomorphisms. -/
theorem under_eq_comap_of_ringEquiv {q : Ideal S} {q' : Ideal S'} (hq : q = q'.comap e2) :
    q.under R = (q'.under R').comap e1 := by
  ext x
  simp [Ideal.mem_comap, hq, h]

include h in
/-- `Ideal.ramificationIdx` is invariant under compatible ring isomorphisms of the base and
the algebra. -/
theorem ramificationIdx_eq_of_ringEquiv {q : Ideal S} {q' : Ideal S'} [q.IsPrime] [q'.IsPrime]
    (hq : q = q'.comap e2) : q'.ramificationIdx R' = q.ramificationIdx R := by
  let φ := Localization.localRingEquiv q q' e2 hq
  have hp := under_eq_comap_of_ringEquiv e1 e2 h hq
  have hcomp : (φ : Localization.AtPrime q →+* Localization.AtPrime q').comp
      (algebraMap R (Localization.AtPrime q)) =
      (algebraMap R' (Localization.AtPrime q')).comp (e1 : R →+* R') := by
    ext x
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [IsScalarTower.algebraMap_apply R S, IsScalarTower.algebraMap_apply R' S']
    have := Localization.localRingHom_to_map q q' (e2 : S →+* S') hq (algebraMap R S x)
    refine this.trans ?_
    rw [RingHom.coe_coe, h]
  have hI : ((q.under R).map (algebraMap R (Localization.AtPrime q))).map
      (φ : Localization.AtPrime q →+* Localization.AtPrime q') =
      (q'.under R').map (algebraMap R' (Localization.AtPrime q')) := by
    rw [Ideal.map_map, hcomp, ← Ideal.map_map, hp]
    congr 1
    exact Ideal.map_comap_of_surjective (e1 : R →+* R') e1.surjective _
  replace hI : ((q.under R).map (algebraMap R (Localization.AtPrime q))).map φ =
      (q'.under R').map (algebraMap R' (Localization.AtPrime q')) := hI
  have key := length_quotient_map_ringEquiv φ
    ((q.under R).map (algebraMap R (Localization.AtPrime q)))
  rw [hI] at key
  rw [Ideal.ramificationIdx_def, Ideal.ramificationIdx_def, key]
include h in
/-- Tame ramification at a prime (`IsTamelyRamifiedAt`) is invariant under compatible ring
isomorphisms of the base and the algebra. -/
theorem IsTamelyRamifiedAt.of_ringEquiv {q : PrimeSpectrum S} {q' : PrimeSpectrum S'}
    (hq : q.asIdeal = q'.asIdeal.comap e2) (H : IsTamelyRamifiedAt R S q) :
    IsTamelyRamifiedAt R' S' q' := by
  have hp := under_eq_comap_of_ringEquiv e1 e2 h hq
  dsimp only [IsTamelyRamifiedAt] at H ⊢
  obtain ⟨H1, H2⟩ := H
  refine ⟨?_, ?_⟩
  · rw [ramificationIdx_eq_of_ringEquiv e1 e2 h hq, natCast_isUnit_residueField_iff]
    rw [natCast_isUnit_residueField_iff, hp, Ideal.mem_comap, map_natCast] at H1
    exact H1
  · let _ : Algebra (Localization.AtPrime (q.asIdeal.under R))
        (Localization.AtPrime q.asIdeal) := Localization.AtPrime.algebraOfLiesOver _ _
    let _ : Algebra (Localization.AtPrime (q'.asIdeal.under R'))
        (Localization.AtPrime q'.asIdeal) := Localization.AtPrime.algebraOfLiesOver _ _
    let ep := Ideal.residueFieldRingEquiv (q.asIdeal.under R) (q'.asIdeal.under R') e1 hp
    let eq := Ideal.residueFieldRingEquiv q.asIdeal q'.asIdeal e2 hq
    refine Algebra.IsSeparable.of_equiv_equiv ep eq ?_
    apply Ideal.ResidueField.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, ep, eq]
    rw [residueField_map_localRingEquiv_algebraMap, residueField_algebraMap_algebraMap,
      residueField_algebraMap_algebraMap, residueField_map_localRingEquiv_algebraMap, h]
end

section
variable {O : Type u} {L : Type v} {O' : Type w} {L' : Type*} [CommRing O] [CommRing L]
  [CommRing O'] [CommRing L'] [Algebra O L] [Algebra O' L']
  (e1 : O ≃+* O') (e2 : L ≃+* L') (h : ∀ x, e2 (algebraMap O L x) = algebraMap O' L' (e1 x))

include h in
/-- Integrality is preserved by compatible ring isomorphisms. -/
theorem isIntegral_map_of_ringEquiv {x : L} (hx : IsIntegral O x) : IsIntegral O' (e2 x) :=
  IsIntegral.map_of_comp_eq (e1 : O →+* O') (e2 : L →+* L') (by ext; simp [h]) hx

/-- The ring isomorphism between integral closures induced by compatible ring isomorphisms. -/
noncomputable def integralClosureRingEquiv :
    integralClosure O L ≃+* integralClosure O' L' where
  toFun x := ⟨e2 x, isIntegral_map_of_ringEquiv e1 e2 h x.2⟩
  invFun y := ⟨e2.symm y, isIntegral_map_of_ringEquiv e1.symm e2.symm (fun x ↦ by
    apply e2.injective
    simp [h]) y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

include h in
/-- **Tame ramification is invariant under compatible ring isomorphisms** of the base and of the
algebra. -/
theorem IsTamelyRamifiedOver.of_ringEquiv (H : IsTamelyRamifiedOver O L) :
    IsTamelyRamifiedOver O' L' := by
  intro m' hm'
  let eC := integralClosureRingEquiv e1 e2 h
  have hC : ∀ x, eC (algebraMap O (integralClosure O L) x) =
      algebraMap O' (integralClosure O' L') (e1 x) := fun x ↦ Subtype.ext (h x)
  let m := m'.comap eC
  have hm : m.IsMaximal := Ideal.comap_isMaximal_of_surjective _ eC.surjective
  exact IsTamelyRamifiedAt.of_ringEquiv e1 eC hC (q := ⟨m, hm.isPrime⟩) rfl (H m hm)
end

/-- **Tameness in codimension one on an affine chart.**  If `D` is cut out by `a` on the affine
open `V` and `f : Y → X ∖ D` is finite and tamely ramified over `X` in codimension one (Stacks
Section 58.31), then the chart `Γ(X, V) → Γ(Y, (f ≫ ι)⁻¹ V)` is tame in codimension one along
`V(a)` in the sense of `ChartTame`. -/
theorem chartTame_of_isTamelyRamifiedInCodimOne {X Y : Scheme.{u}} {D : X.IdealSheafData}
    {V : X.affineOpens} {a : Γ(X, V)} (hDa : D.ideal V = Ideal.span {a})
    (f : Y ⟶ complementOpen D) [IsFinite f]
    (htame : IsTamelyRamifiedInCodimOne (complementOpen D) f) :
    letI := ((f ≫ (complementOpen D).ι).app V.1).hom.toAlgebra
    ChartTame a Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) := by
  let _ := ((f ≫ (complementOpen D).ι).app V.1).hom.toAlgebra
  intro p hp hap hdim
  have hgV : IsAffineOpen ((f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) :=
    (isAffineOpen_preimage_ι_of_ideal_eq hDa).preimage f
  let pt : PrimeSpectrum Γ(X, V.1) := ⟨p, hp⟩
  let ξ : X := V.2.fromSpec pt
  have hξV : ξ ∈ V.1 := by
    rw [← SetLike.mem_coe, ← V.2.range_fromSpec]
    exact Set.mem_range_self pt
  let xU : V.1 := ⟨ξ, hξV⟩
  have hprime : V.2.primeIdealOf xU = pt := IsAffineOpen.primeIdealOf_fromSpec V.2 pt
  let _ : Algebra Γ(X, V.1) (X.presheaf.stalk ξ) := X.presheaf.algebra_section_stalk xU
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk ξ) p := by
    have := V.2.isLocalization_stalk xU
    rw [hprime] at this
    exact this
  have hξD : ξ ∉ complementOpen D := by
    change ¬ (ξ ∉ D.support)
    rw [not_not, mem_support_iff_of_ideal_eq hDa hξV]
    intro hb
    have : pt ∈ V.2.fromSpec ⁻¹ᵁ X.basicOpen a := hb
    rw [V.2.fromSpec_preimage_basicOpen] at this
    exact this hap
  let e1 : X.presheaf.stalk ξ ≃ₐ[Γ(X, V.1)] Localization.AtPrime p :=
    IsLocalization.algEquiv p.primeCompl _ _
  have hdimO : ringKrullDim (X.presheaf.stalk ξ) = 1 := by
    rw [ringKrullDim_eq_of_ringEquiv e1.toRingEquiv]
    exact hdim
  have H := htame ξ hξD hdimO
  let O := X.presheaf.stalk ξ
  let K := FractionRing O
  have ht : specFractionFieldToScheme X ξ =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) K)) ≫ V.2.fromSpec := by
    rw [specFractionFieldToScheme, ← V.2.fromSpecStalk_eq_fromSpecStalk hξV]
    change _ ≫ Spec.map (X.presheaf.germ _ ξ hξV) ≫ V.2.fromSpec = _
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
  have hP := isPullback_tensor_fromSpec (f ≫ (complementOpen D).ι) V.2 hgV K
  rw [← ht] at hP
  let ψ := hP.isoPullback
  have hψ := hP.isoPullback_hom_snd
  let Γψ : Γ(pullback (f ≫ (complementOpen D).ι) (specFractionFieldToScheme X ξ), ⊤) ≅ _ :=
    { hom := ψ.hom.appTop
      inv := ψ.inv.appTop
      hom_inv_id := by rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id]; rfl
      inv_hom_id := by rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id]; rfl }
  let E := (Γψ ≪≫ Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv
  have hE : ∀ k : K, E (algebraMap K (genericFibreRing (complementOpen D) f ξ) k) =
      algebraMap K _ k := by
    intro k
    have key : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (pullback.snd (f ≫ (complementOpen D).ι) (specFractionFieldToScheme X ξ)).appTop ≫
          ψ.hom.appTop ≫ (Scheme.ΓSpecIso _).hom = CommRingCat.ofHom (algebraMap K _) := by
      rw [← Category.assoc
          (pullback.snd (f ≫ (complementOpen D).ι) (specFractionFieldToScheme X ξ)).appTop,
        ← Scheme.Hom.comp_appTop, hψ,
        Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    exact congr($key k)
  let M := Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1)
  let E' : genericFibreRing (complementOpen D) f ξ ≃+* K ⊗[Γ(X, V.1)] M := E
  let K' := FractionRing (Localization.AtPrime p)
  let eKr : K ≃+* K' := IsLocalization.ringEquivOfRingEquiv K K' e1.toRingEquiv
    (MulEquivClass.map_nonZeroDivisors e1.toRingEquiv)
  have heKr : ∀ x : O, eKr (algebraMap O K x) =
      algebraMap (Localization.AtPrime p) K' (e1 x) := fun x ↦
    IsLocalization.ringEquivOfRingEquiv_eq _ x
  let eK : K ≃ₐ[Γ(X, V.1)] K' := AlgEquiv.ofRingEquiv (f := eKr) fun r ↦ by
    rw [IsScalarTower.algebraMap_apply Γ(X, V.1) O K, heKr, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
  let E2 : K ⊗[Γ(X, V.1)] M ≃+* K' ⊗[Γ(X, V.1)] M :=
    (Algebra.TensorProduct.congr eK (AlgEquiv.refl : M ≃ₐ[Γ(X, V.1)] M)).toRingEquiv
  refine IsTamelyRamifiedOver.of_ringEquiv e1.toRingEquiv (E'.trans E2) (fun x ↦ ?_) H
  change E2 (E (algebraMap K (genericFibreRing (complementOpen D) f ξ)
    (algebraMap O K x))) = _
  rw [hE, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply]
  change Algebra.TensorProduct.congr eK AlgEquiv.refl (_ ⊗ₜ 1) = _
  rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  simp [eK, heKr]
  rfl

end Pcf.Stacks.SchemeLevel

