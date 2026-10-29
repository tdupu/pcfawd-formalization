/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Unnormalized.SchemeBranch
public import Pcf.Unnormalized.SchemeBranchZero
public import Pcf.Bounding.CriticalLoci
public import Pcf.Stacks.Purity.Tag0BMBScheme
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Etale.Locus

/-!
# Affine computation of the unnormalized branch loci

For an affine map `Spec S ⟶ Spec R` induced by an algebra `R → S`, this file
translates the scheme predicates `schemeUnnormalizedBranchZero` and
`schemeUnnormalizedBranchOne` of `paper-p.tex`, Definition `def:branch-loci`,
into commutative algebra:

* the intrinsic scheme fibre over `p` is reduced iff `κ(p) ⊗[R] S` is reduced,
  and for maximal `p` iff `S ⧸ pS` is reduced;
* the stalk map at `q` is formally étale iff `R → S` is étale at `q`;
* for a finite algebra in characteristic zero, a nonreduced fibre has a
  non-étale point above it.

These are used for the concrete curves of Example `ex:loci-compared`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.AffineLociBridge

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

set_option linter.style.haveILetI false

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The affine scheme map induced by `R → S`. -/
noncomputable abbrev specMap : Spec (.of S) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R S))

theorem specMap_apply (q : PrimeSpectrum S) :
    specMap R S q = PrimeSpectrum.comap (algebraMap R S) q := rfl

/-- The intrinsic fibre of `Spec S ⟶ Spec R` over `p` is reduced iff the
fibre ring `κ(p) ⊗[R] S` is reduced. -/
theorem specFiber_isReduced_iff (p : PrimeSpectrum R) :
    AlgebraicGeometry.IsReduced ((specMap R S).fiber p) ↔
      _root_.IsReduced (p.asIdeal.Fiber S) := by
  let e := Spec.fiberToSpecResidueFieldIso R S p
  constructor
  · intro hred
    letI : AlgebraicGeometry.IsReduced ((specMap R S).fiber p) := hred
    have hspec : AlgebraicGeometry.IsReduced (Spec (.of (p.asIdeal.Fiber S))) :=
      @isReduced_of_isOpenImmersion _ _ e.inv.left inferInstance hred
    exact (affine_isReduced_iff _).mp hspec
  · intro hring
    letI : _root_.IsReduced (p.asIdeal.Fiber S) := hring
    have hspec : AlgebraicGeometry.IsReduced (Spec (.of (p.asIdeal.Fiber S))) :=
      (affine_isReduced_iff _).mpr hring
    exact @isReduced_of_isOpenImmersion _ _ e.hom.left inferInstance hspec

/-- At a maximal ideal the fibre ring is the quotient `S ⧸ mS`. -/
noncomputable def fiberRingEquivQuotient (m : Ideal R) [m.IsMaximal] :
    m.Fiber S ≃+* S ⧸ m.map (algebraMap R S) := by
  let eκ : (R ⧸ m) ≃ₐ[R] m.ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ m) m.ResidueField)
      m.bijective_algebraMap_quotient_residueField
  let e₁ : m.Fiber S ≃ₐ[R] (R ⧸ m) ⊗[R] S :=
    Algebra.TensorProduct.congr eκ.symm AlgEquiv.refl
  let e₂ : (R ⧸ m) ⊗[R] S ≃ₐ[R] S ⊗[R] (R ⧸ m) := Algebra.TensorProduct.comm R _ _
  let e₃ : S ⊗[R] (R ⧸ m) ≃+* S ⧸ m.map (algebraMap R S) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S m).symm.toRingEquiv
  exact e₁.toRingEquiv.trans (e₂.toRingEquiv.trans e₃)

theorem fiber_isReduced_iff_quotient (m : Ideal R) [m.IsMaximal] :
    _root_.IsReduced (m.Fiber S) ↔ _root_.IsReduced (S ⧸ m.map (algebraMap R S)) := by
  let e := fiberRingEquivQuotient R S m
  constructor
  · intro h
    exact isReduced_of_injective e.symm.toRingHom e.symm.injective
  · intro h
    exact isReduced_of_injective e.toRingHom e.injective

/-- The prime ideal underlying a divisor point of an affine scheme. -/
abbrev divisorPrime (E : Pcf.SchemeDivisorPoint (Spec (.of R))) : PrimeSpectrum R := E.1

/-- Membership of a target divisor in `branch₀` for an affine map: the fibre
ring is not reduced. -/
theorem mem_branchZero_iff (E : Pcf.SchemeDivisorPoint (Spec (.of R))) :
    E ∈ Pcf.schemeUnnormalizedBranchZero (specMap R S) ↔
      ¬ _root_.IsReduced ((divisorPrime R E).asIdeal.Fiber S) := by
  exact not_congr (specFiber_isReduced_iff R S (divisorPrime R E))

/-- Membership in `branch₀` at a maximal ideal: `S ⧸ mS` is not reduced. -/
theorem mem_branchZero_iff_quotient (E : Pcf.SchemeDivisorPoint (Spec (.of R)))
    [(divisorPrime R E).asIdeal.IsMaximal] :
    E ∈ Pcf.schemeUnnormalizedBranchZero (specMap R S) ↔
      ¬ _root_.IsReduced (S ⧸ (divisorPrime R E).asIdeal.map (algebraMap R S)) := by
  rw [mem_branchZero_iff, fiber_isReduced_iff_quotient]

/-- The actual stalk map of `Spec S ⟶ Spec R` at `q` is formally étale iff
`R → S` is étale at `q`. -/
theorem stalk_formallyEtale_iff (q : PrimeSpectrum S) :
    ((specMap R S).stalkMap q).hom.FormallyEtale ↔ Algebra.IsEtaleAt R q.asIdeal := by
  let p := PrimeSpectrum.comap (algebraMap R S) q
  have hlies : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  trans (Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R S) rfl).FormallyEtale
  · exact Pcf.formallyEtale_respectsIso.arrow_mk_iso_iff
      (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom (algebraMap R S)) q)
  · change Algebra.FormallyEtale (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) ↔ _
    exact Algebra.FormallyEtale.iff_restrictScalars.symm

/-- Membership of a target divisor in `branch₁` for an affine map. -/
theorem mem_branchOne_iff (E : Pcf.SchemeDivisorPoint (Spec (.of R))) :
    E ∈ Pcf.schemeUnnormalizedBranchOne (specMap R S) ↔
      ∃ q : PrimeSpectrum S, PrimeSpectrum.comap (algebraMap R S) q = E.1 ∧
        ¬ Algebra.IsEtaleAt R q.asIdeal := by
  constructor
  · rintro ⟨x, hx, hnot⟩
    exact ⟨x, hx, fun h => hnot ((stalk_formallyEtale_iff R S x).mpr h)⟩
  · rintro ⟨q, hq, hnot⟩
    exact ⟨q, hq, fun h => hnot ((stalk_formallyEtale_iff R S q).mp h)⟩

/-- Over a characteristic-zero point of a finite algebra, a nonreduced fibre
ring has a non-étale prime above it. -/
theorem exists_not_isEtaleAt_of_fiber_not_isReduced [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] [CharZero p.ResidueField]
    (h : ¬ _root_.IsReduced (p.Fiber S)) :
    ∃ Q : p.primesOver S, ¬ Algebra.IsEtaleAt R Q.1 := by
  by_contra hall
  push Not at hall
  apply h
  apply (Pcf.finiteFiber_isReduced_iff_forall_unramifiedAt_charZero (R := R) (S := S) p).mpr
  intro Q
  haveI : Q.1.IsPrime := Q.2.1
  haveI := hall Q
  change Algebra.FormallyUnramified R (Localization.AtPrime Q.1)
  infer_instance

/-- A nonreduced fibre (`branch₀`) forces a non-étale point (`branch₁`), for a
finite algebra in characteristic zero. -/
theorem mem_branchOne_of_mem_branchZero [Module.Finite R S]
    (E : Pcf.SchemeDivisorPoint (Spec (.of R)))
    [CharZero (divisorPrime R E).asIdeal.ResidueField]
    (hE : E ∈ Pcf.schemeUnnormalizedBranchZero (specMap R S)) :
    E ∈ Pcf.schemeUnnormalizedBranchOne (specMap R S) := by
  rw [mem_branchZero_iff] at hE
  obtain ⟨Q, hQ⟩ := exists_not_isEtaleAt_of_fiber_not_isReduced R S (divisorPrime R E).asIdeal hE
  haveI : Q.1.IsPrime := Q.2.1
  rw [mem_branchOne_iff]
  refine ⟨⟨Q.1, Q.2.1⟩, ?_, hQ⟩
  apply PrimeSpectrum.ext
  exact (Q.2.2.over).symm

omit [Algebra R S] in
/-- Pointwise Stacks étaleness gives a formally étale stalk. -/
theorem stalk_formallyEtale_of_isStacksEtaleAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (h : Pcf.Stacks.IsStacksEtaleAt f x) : (f.stalkMap x).hom.FormallyEtale := by
  obtain ⟨U, hU, V, hV, hUV, hx, he⟩ := h
  letI := (f.appLE V U hUV).hom.toAlgebra
  have hE : Algebra.Etale Γ(Y, V) Γ(X, U) := RingHom.etale_algebraMap.mp he
  rw [Pcf.formallyEtale_stalkMap_iff V hV U hU hUV hx]
  rw [Algebra.etaleLocus_eq_univ_iff.mpr inferInstance]
  trivial

/-- The `R`-algebra structure on the localization `S[φ(x)⁻¹]` exhibits it as
the localization `R[x⁻¹]` when the induced map is bijective. -/
theorem isLocalization_away_of_awayMap_bijective (x : R)
    (hbij : Function.Bijective (Localization.awayMap (algebraMap R S) x)) :
    IsLocalization.Away x (Localization.Away (algebraMap R S x)) := by
  let e : Localization.Away x ≃ₐ[R] Localization.Away (algebraMap R S x) :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective _ hbij) (fun r => by
      change Localization.awayMap (algebraMap R S) x (algebraMap R _ r) = _
      rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
      exact (IsScalarTower.algebraMap_apply R S _ r).symm)
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers x) e

end Pcf.Examples.PaperP.AffineLociBridge

#print axioms Pcf.Examples.PaperP.AffineLociBridge.mem_branchZero_iff_quotient
#print axioms Pcf.Examples.PaperP.AffineLociBridge.mem_branchOne_iff
#print axioms Pcf.Examples.PaperP.AffineLociBridge.mem_branchOne_of_mem_branchZero
#print axioms Pcf.Examples.PaperP.AffineLociBridge.stalk_formallyEtale_of_isStacksEtaleAt
#print axioms Pcf.Examples.PaperP.AffineLociBridge.isLocalization_away_of_awayMap_bijective
