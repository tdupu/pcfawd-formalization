/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.ReynoldsSpecialization
public import Pcf.PrimeToPMonodromy
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.GroupTheory.Coset.Card

/-!
# Finite-group invariants on a centre's fibre

The proof of `latex/paper-p.tex`, Lemma `lem:allcodim-monodromy`,
specializes the integral closure at the function field of an arbitrary
centre and reduces modulo the nilradical. The results here specialize
Reynolds exactness to an actual group-stable ideal of a commutative
algebra. In particular, an invariant class modulo that ideal comes
from an invariant element before reduction.
-/

@[expose] public section

namespace Pcf

universe u v w

set_option linter.style.haveILetI false

variable {k : Type u} {B : Type v} {G : Type w}
  [Field k] [CommRing B] [Algebra k B]
  [Group G] [Fintype G]

/-- The quotient representation associated to a group-stable ideal.
The quotient is taken as a `k`-module, so it is the additive module
underlying the usual quotient algebra. -/
def stableIdealSubrepresentation
    (ρ : Representation k G B) (I : Ideal B)
    (hI : ∀ (g : G) (b : B), b ∈ I → ρ g b ∈ I) :
    Subrepresentation ρ where
  toSubmodule := I.restrictScalars k
  apply_mem_toSubmodule g _ hb := hI g _ hb

/-- Reynolds averaging lifts invariant classes through the quotient by
a stable ideal, without requiring flatness of the algebra over its
invariant subring. This is the reduction step of
`lem:allcodim-monodromy` for the nilradical ideal. -/
theorem invariant_lift_mod_stable_ideal
    (p : ℕ) (hp : p.Prime) [CharP k p]
    (horder : (Fintype.card G).Coprime p)
    (ρ : Representation k G B) (I : Ideal B)
    (hI : ∀ (g : G) (b : B), b ∈ I → ρ g b ∈ I)
    (w : B ⧸ (stableIdealSubrepresentation ρ I hI).toSubmodule)
    (hw : w ∈ (stableIdealSubrepresentation ρ I hI).quotient.invariants) :
    ∃ b : B, b ∈ ρ.invariants ∧
      (Submodule.mkQ (stableIdealSubrepresentation ρ I hI).toSubmodule) b = w := by
  let S := stableIdealSubrepresentation ρ I hI
  exact invariant_lift_of_surjective_charP p hp horder
    ρ S.quotient (Submodule.mkQ S.toSubmodule)
    (Submodule.mkQ_surjective S.toSubmodule)
    (fun g b => by exact (S.quotient_apply_mk g b).symm) w hw

/-- If the only invariant elements of the algebra are scalars, the same
holds after reduction by any stable ideal. This is the precise
`(C_red)^G=F` surjectivity step in the manuscript, stated on the
underlying quotient module. -/
theorem invariant_mod_stable_ideal_is_scalar
    (p : ℕ) (hp : p.Prime) [CharP k p]
    (horder : (Fintype.card G).Coprime p)
    (ρ : Representation k G B) (I : Ideal B)
    (hI : ∀ (g : G) (b : B), b ∈ I → ρ g b ∈ I)
    (hscalar : ∀ b : B, b ∈ ρ.invariants →
      ∃ a : k, algebraMap k B a = b)
    (w : B ⧸ (stableIdealSubrepresentation ρ I hI).toSubmodule)
    (hw : w ∈ (stableIdealSubrepresentation ρ I hI).quotient.invariants) :
    ∃ a : k,
      (Submodule.mkQ (stableIdealSubrepresentation ρ I hI).toSubmodule)
        (algebraMap k B a) = w := by
  obtain ⟨b, hb, hbw⟩ :=
    invariant_lift_mod_stable_ideal p hp horder ρ I hI w hw
  obtain ⟨a, rfl⟩ := hscalar b hb
  exact ⟨a, hbw⟩

/-- The fixed-field step for a field factor of the reduced fibre.
When the action is faithful, the factor is itself a finite Galois
extension whose degree is the group order, hence prime to `p`.
For a stabilizer with kernel, apply this to its faithful quotient. -/
theorem isPrimeToPMonodromy_of_faithful_fixed_field
    (p : ℕ) (F : Type u) (L : Type v) (H : Type w)
    [Field F] [Field L] [Algebra F L]
    [Group H] [Fintype H] [MulSemiringAction H L]
    [FaithfulSMul H L] [SMulCommClass H F L]
    [Algebra.IsInvariant F L H]
    (horder : (Fintype.card H).Coprime p) :
    IsPrimeToPMonodromy.{u, v, v} p F L := by
  letI : IsGaloisGroup H F L := ⟨inferInstance, inferInstance, inferInstance⟩
  letI : FiniteDimensional F L := IsGaloisGroup.finiteDimensional H F L
  letI : IsGalois F L := IsGaloisGroup.isGalois H F L
  have hdegree : (Module.finrank F L).Coprime p := by
    rw [← IsGaloisGroup.card_eq_finrank H F L, Nat.card_eq_fintype_card]
    exact horder
  exact isPrimeToPMonodromy_of_embedding_into_galois p F L L
    (AlgHom.id F L) hdegree

/-- A finite (possibly nonfaithful) prime-to-`p` group acting on a
field with fixed field `F` gives prime-to-`p` monodromy. The kernel
of the action is removed before applying the faithful fixed-field
theorem. -/
theorem isPrimeToPMonodromy_of_fixed_field
    (p : ℕ) (F : Type u) (L : Type v) (H : Type w)
    [Field F] [Field L] [Algebra F L]
    [Group H] [Fintype H] [MulSemiringAction H L]
    [SMulCommClass H F L] [Algebra.IsInvariant F L H]
    (horder : (Fintype.card H).Coprime p) :
    IsPrimeToPMonodromy.{u, v, v} p F L := by
  let f : H →* L ≃ₐ[F] L := MulSemiringAction.toAlgAut H F L
  let N : Subgroup H := f.ker
  let Q := H ⧸ N
  letI : MulSemiringAction Q L :=
    MulSemiringAction.compHom L (QuotientGroup.kerLift f)
  letI : FaithfulSMul Q L := ⟨fun {q₁ q₂} => by
    induction q₁, q₂ using Quotient.inductionOn₂ with
    | _ g₁ g₂ =>
      intro h
      rwa [QuotientGroup.eq, MonoidHom.mem_ker, map_mul, map_inv,
        inv_mul_eq_one, AlgEquiv.ext_iff]⟩
  letI : SMulCommClass Q F L := ⟨fun q a x => by
    induction q using Quotient.inductionOn with
    | _ g => exact smul_comm g a x⟩
  letI : Algebra.IsInvariant F L Q := ⟨fun x hx => by
    apply Algebra.IsInvariant.isInvariant (G := H) x
    intro g
    have hq := hx (QuotientGroup.mk g)
    change (QuotientGroup.kerLift f (QuotientGroup.mk g)) x = x at hq
    simpa [f, QuotientGroup.kerLift_mk] using hq⟩
  letI : Fintype Q := Fintype.ofFinite Q
  have hQ : (Fintype.card Q).Coprime p :=
    Nat.Coprime.of_dvd_left
      (by simpa only [Nat.card_eq_fintype_card] using N.card_quotient_dvd_card)
      horder
  exact isPrimeToPMonodromy_of_faithful_fixed_field p F L Q hQ

/-- Final field-theoretic step of the centre argument: an arbitrary
subfield of a specialized Galois factor inherits prime-to-`p`
monodromy, even when that subfield is not itself Galois. -/
theorem isPrimeToPMonodromy_of_embedding_in_fixed_field_factor
    (p : ℕ) (F : Type u) (E L : Type v) (H : Type w)
    [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra F L]
    [Group H] [Fintype H] [MulSemiringAction H L]
    [SMulCommClass H F L] [Algebra.IsInvariant F L H]
    (horder : (Fintype.card H).Coprime p)
    (ι : E →ₐ[F] L) :
    IsPrimeToPMonodromy.{u, v, v} p F E :=
  isPrimeToPMonodromy_of_algHom p F E L
    (isPrimeToPMonodromy_of_fixed_field p F L H horder) ι

#print axioms invariant_lift_mod_stable_ideal
#print axioms invariant_mod_stable_ideal_is_scalar
#print axioms isPrimeToPMonodromy_of_faithful_fixed_field
#print axioms isPrimeToPMonodromy_of_fixed_field
#print axioms isPrimeToPMonodromy_of_embedding_in_fixed_field_factor

end Pcf
