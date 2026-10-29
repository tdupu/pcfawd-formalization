/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.PinchedNormalization
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The pinched plane as a pushout (Ferrand pinching), affine part

For `paper-p.tex`, Example `ex:pinched`: "`X` is the pushout of `𝔸² ← {p₁, p₂} → Spec k` …;
its ring of functions is the fibre product `k[z, w] ×_{k × k} k`, which is `R`".

* `isPullback_ring`: the square `R → k[z, w]`, `R → k` (`h ↦ h(p₁)`), `k[z, w] → k × k`
  (`h ↦ (h(p₁), h(p₂))`), `k → k × k` (diagonal) is a pullback in `CommRingCat`; that is,
  `R = k[z, w] ×_{k × k} k`.
* `isPushout_affineScheme`: hence `X = Spec R` is the pushout of
  `𝔸² ← Spec(k × k) → Spec k` in the category `AffineScheme` (`Spec` is an equivalence
  `CommRingCatᵒᵖ ≌ AffineScheme`).
* `existsUnique_desc_of_isAffine`: the pushout property in `Scheme` for affine test objects.

The statement for arbitrary test schemes (Stacks 0ET0 / 0E25) is not proved here.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.PinchedPushout

open AlgebraicGeometry CategoryTheory Limits MvPolynomial Pcf.Examples.Pinched
open Pcf.Examples.PaperP.PinchedNormalization

set_option linter.unusedSectionVars false

universe u

variable (k : Type u) [Field k] [CharZero k]

local notation "R" => PinchedRing k
local notation "S" => PlaneRing k

/-- `k[z, w] → k × k`, `h ↦ (h(p₁), h(p₂))`: the closed immersion `{p₁, p₂} → 𝔸²`. -/
noncomputable def evalPair : S →+* k × k :=
  (evalTwoOne k).toRingHom.prod (evalNegTwoOne k).toRingHom

/-- The diagonal `k → k × k`: the map `{p₁, p₂} → Spec k`. -/
noncomputable def diagK : k →+* k × k := (RingHom.id k).prod (RingHom.id k)

/-- `R → k`, `h ↦ h(p₁) = h(p₂)`: the point `o : Spec k → X`. -/
noncomputable def evalO : R →+* k := (evalTwoOne k).toRingHom.comp (algebraMap R S)

theorem evalPair_comp :
    (evalPair k).comp (algebraMap R S) = (diagK k).comp (evalO k) := by
  ext r
  · rfl
  · exact (PinchedRing.val_mem k r).symm

/-- The pullback cone `R` over `k[z, w] → k × k ← k`. -/
noncomputable def ringPullbackCone :
    PullbackCone (CommRingCat.ofHom (evalPair k)) (CommRingCat.ofHom (diagK k)) :=
  PullbackCone.mk (W := CommRingCat.of R) (CommRingCat.ofHom (algebraMap R S))
    (CommRingCat.ofHom (evalO k)) (by
      ext1
      exact evalPair_comp k)

theorem cond_apply {T : CommRingCat.{u}}
    {a : T ⟶ CommRingCat.of S} {b : T ⟶ CommRingCat.of k}
    (h : a ≫ CommRingCat.ofHom (evalPair k) = b ≫ CommRingCat.ofHom (diagK k)) (x : T) :
    evalTwoOne k (a x) = b x ∧ evalNegTwoOne k (a x) = b x := by
  have := congrArg (fun f => f.hom x) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  exact Prod.ext_iff.mp this

/-- **`R = k[z, w] ×_{k × k} k`**: the cone is a limit. -/
noncomputable def ringPullbackConeIsLimit : IsLimit (ringPullbackCone k) :=
  PullbackCone.IsLimit.mk _
    (fun s => CommRingCat.ofHom ((s.fst.hom).codRestrict (pinchedAlg k) fun x => by
      obtain ⟨h1, h2⟩ := cond_apply k s.condition x
      exact h1.trans h2.symm))
    (fun s => by ext x; rfl)
    (fun s => by
      ext x
      exact (cond_apply k s.condition x).1)
    (fun s m h1 _ => by
      ext x
      apply Subtype.val_injective (p := fun h => h ∈ pinchedAlg k)
      exact congrArg (fun f => f.hom x) h1)

/-- `paper-p.tex` correspondence: Example A.9 (`ex:pinched`). -/
theorem isPullback_ring :
    IsPullback (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (evalO k))
      (CommRingCat.ofHom (evalPair k)) (CommRingCat.ofHom (diagK k)) :=
  IsPullback.of_isLimit (ringPullbackConeIsLimit k)

instance affineSpec_isEquivalence : AffineScheme.Spec.{u}.IsEquivalence where

/-- **`X` is the pushout of `𝔸² ← {p₁, p₂} → Spec k` in affine schemes.** -/
theorem isPushout_affineScheme :
    IsPushout (AffineScheme.Spec.map (CommRingCat.ofHom (evalPair k)).op)
      (AffineScheme.Spec.map (CommRingCat.ofHom (diagK k)).op)
      (AffineScheme.Spec.map (CommRingCat.ofHom (algebraMap R S)).op)
      (AffineScheme.Spec.map (CommRingCat.ofHom (evalO k)).op) :=
  (isPullback_ring k).op.flip.map AffineScheme.Spec

#print axioms isPullback_ring
#print axioms isPushout_affineScheme

/-- **Pushout property in `Scheme`, for affine test schemes**: given `a : 𝔸² → T` and
`b : Spec k → T` agreeing on `{p₁, p₂}`, with `T` affine, there is a unique `φ : X → T`
with `φ ∘ ν = a` and `φ ∘ o = b`. -/
theorem existsUnique_desc_of_isAffine {T : Scheme.{u}} [IsAffine T]
    (a : Spec (CommRingCat.of S) ⟶ T) (b : Spec (CommRingCat.of k) ⟶ T)
    (h : Spec.map (CommRingCat.ofHom (evalPair k)) ≫ a =
      Spec.map (CommRingCat.ofHom (diagK k)) ≫ b) :
    ∃! φ : Spec (CommRingCat.of R) ⟶ T,
      Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ φ = a ∧
        Spec.map (CommRingCat.ofHom (evalO k)) ≫ φ = b := by
  have P := (isPullback_ring k).op.flip
  let F := Spec.fullyFaithful
  let a' := F.preimage (a ≫ T.isoSpec.hom)
  let b' := F.preimage (b ≫ T.isoSpec.hom)
  have ha' : Spec.map a'.unop = a ≫ T.isoSpec.hom := F.map_preimage _
  have hb' : Spec.map b'.unop = b ≫ T.isoSpec.hom := F.map_preimage _
  have hw : (CommRingCat.ofHom (evalPair k)).op ≫ a' = (CommRingCat.ofHom (diagK k)).op ≫ b' := by
    apply F.map_injective
    change Spec.map (a'.unop ≫ CommRingCat.ofHom (evalPair k)) =
      Spec.map (b'.unop ≫ CommRingCat.ofHom (diagK k))
    rw [Spec.map_comp, Spec.map_comp, ha', hb', ← Category.assoc, h, Category.assoc]
  refine ⟨Spec.map (P.desc a' b' hw).unop ≫ T.isoSpec.inv, ⟨?_, ?_⟩, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp]
    change Spec.map ((CommRingCat.ofHom (algebraMap R S)).op ≫ P.desc a' b' hw).unop ≫ _ = _
    rw [P.inl_desc, ha', Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [← Category.assoc, ← Spec.map_comp]
    change Spec.map ((CommRingCat.ofHom (evalO k)).op ≫ P.desc a' b' hw).unop ≫ _ = _
    rw [P.inr_desc, hb', Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rintro φ ⟨h1, h2⟩
    rw [Iso.eq_comp_inv]
    let φ' := F.preimage (φ ≫ T.isoSpec.hom)
    have hφ' : Spec.map φ'.unop = φ ≫ T.isoSpec.hom := F.map_preimage _
    rw [← hφ']
    congr 1
    congr 1
    apply P.hom_ext
    · rw [P.inl_desc]
      apply F.map_injective
      change Spec.map (φ'.unop ≫ CommRingCat.ofHom (algebraMap R S)) = Spec.map a'.unop
      rw [Spec.map_comp, hφ', ha', ← Category.assoc, h1]
    · rw [P.inr_desc]
      apply F.map_injective
      change Spec.map (φ'.unop ≫ CommRingCat.ofHom (evalO k)) = Spec.map b'.unop
      rw [Spec.map_comp, hφ', hb', ← Category.assoc, h2]

#print axioms existsUnique_desc_of_isAffine

end Pcf.Examples.PaperP.PinchedPushout
