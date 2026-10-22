/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.CoverDescent
public import Pcf.Bounding.GlobalNormalizationMorphism
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Tower

/-!
# Finite comparison maps in positive characteristic

The local DVR calculation below is the constant-`δ` input for the purely
inseparable comparison in `latex/paper-p.tex`, Lemma
`lem:pcf-transfer-charp`. The theorem treats the residue extension as an
actual purely inseparable field extension and derives its `δ` from the
fundamental identity, rather than postulating that identity.
-/

@[expose] public section

namespace Pcf

set_option linter.style.haveILetI false

/-- At the unique prime of a finite local extension of Dedekind domains,
ramification index times inseparable residue degree is the generic field
degree when the residue extension is purely inseparable. This is the
local calculation `δ_ρ(D)=q` in the proof of `paper-p.tex`, Lemma
`lem:pcf-transfer-charp`. -/
theorem local_purelyInseparable_delta_eq_finrank
    (R S K L : Type*)
    [CommRing R] [IsDedekindDomain R] [IsLocalRing R]
    [CommRing S] [IsDedekindDomain S] [IsLocalRing S]
    [Algebra R S] [Module.Finite R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L]
    [IsScalarTower R K L]
    (p : Ideal R) [p.IsMaximal] (hp0 : p ≠ ⊥)
    [(IsLocalRing.maximalIdeal S).LiesOver p] :
    letI := Localization.AtPrime.algebraOfLiesOver p (IsLocalRing.maximalIdeal S)
    IsPurelyInseparable p.ResidueField
      (IsLocalRing.maximalIdeal S).ResidueField →
    Ideal.ramificationIdx' p (IsLocalRing.maximalIdeal S) *
      Field.finInsepDegree p.ResidueField
        (IsLocalRing.maximalIdeal S).ResidueField =
        Module.finrank K L := by
  let P := IsLocalRing.maximalIdeal S
  letI := Localization.AtPrime.algebraOfLiesOver p P
  intro hpure
  letI : IsPurelyInseparable p.ResidueField P.ResidueField := hpure
  have hfund := Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
    (R := R) (S := S) (K := K) (L := L) (p := p) hp0
  rw [Ideal.inertiaDeg'_eq_inertiaDeg, Ideal.inertiaDeg_eq p P] at hfund
  rw [IsPurelyInseparable.finInsepDegree_eq p.ResidueField P.ResidueField]
  exact hfund

/-- Inseparable-degree cancellation for the two function-field towers of a
commuting finite comparison square. `A` is the image of the upstairs map,
`B` the comparison subfield, and the equality of comparison degrees comes
from the isomorphism induced by the upstairs pullback. The argument is the
first paragraph of `paper-p.tex`, Lemma `lem:pcf-transfer-charp`. -/
theorem isSeparable_of_insepDegree_diamond
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    (A B : IntermediateField F E)
    [FiniteDimensional F A] [FiniteDimensional F B]
    [FiniteDimensional B E]
    (hsep : Algebra.IsSeparable A E)
    (hcomparison : Field.finInsepDegree F A = Field.finInsepDegree B E) :
    Algebra.IsSeparable F B := by
  letI : Algebra.IsSeparable A E := hsep
  have hA := Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic F A E
  have hB := Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic F B E
  rw [Algebra.IsSeparable.finInsepDegree_eq A E, mul_one] at hA
  have hprod : Field.finInsepDegree F B * Field.finInsepDegree B E =
      1 * Field.finInsepDegree B E := by
    calc
      _ = Field.finInsepDegree F E := hB
      _ = Field.finInsepDegree B E := hA.symm.trans hcomparison
      _ = 1 * Field.finInsepDegree B E := (one_mul _).symm
  have hpositive : 0 < Field.finInsepDegree B E := Nat.pos_of_ne_zero (NeZero.ne _)
  have hdegree : Field.finInsepDegree F B = 1 :=
    Nat.mul_right_cancel hpositive hprod
  exact (isSeparable_iff_finInsepDegree_eq_one F B).mpr hdegree

/-! ### The purely inseparable comparison on divisors -/

universe u v

/-- Divisor dynamics with the positive-characteristic local degree
`δ=e·[κ'/κ]_{insep}`. The geometric constructor from a finite separable
endomorphism is a separate step. -/
structure DeltaDynamics (P : Type u) where
  step : P → P
  delta : P → ℕ

namespace DeltaDynamics

variable {P : Type u} {Q : Type v} (D : DeltaDynamics P) (E : DeltaDynamics Q)

/-- Critical divisors for the weighted local degree `δ`. -/
def critical : Set P := {d | 1 < D.delta d}

/-- Images of critical divisors. -/
def branch : Set P := D.step '' D.critical

/-- The postcritical divisor set. -/
def postcriticalSet : Set P := ⋃ n : ℕ, D.step^[n] '' D.branch

def IsPCF : Prop := D.postcriticalSet.Finite

/-- The arithmetic cover-descent lemma only needs positive local weights;
we reuse its divisor system with `δ` as those weights. This construction
does not assert that `δ` equals the ramification index in characteristic
`p`. -/
def toDivisorDynamics (hpos : ∀ d, 0 < D.delta d)
    (hsurj : Function.Surjective D.step)
    (hbranch : D.branch.Finite) : DivisorDynamics P where
  step := D.step
  ramificationIdx := D.delta
  ramificationIdx_pos := hpos
  step_surjective := hsurj
  step_image_ramified_finite := by
    have heq : {Q | ∃ Q', D.step Q' = Q ∧ 1 < D.delta Q'} = D.branch := by
      ext d
      simp [branch, critical, Set.mem_image, and_comm]
    rw [heq]
    exact hbranch

@[simp] theorem toDivisorDynamics_branch
    (hpos : ∀ d, 0 < D.delta d)
    (hsurj : Function.Surjective D.step)
    (hbranch : D.branch.Finite) :
    (D.toDivisorDynamics hpos hsurj hbranch).branch = D.branch := by
  ext d
  simp [DivisorDynamics.branch, branch, critical, toDivisorDynamics,
    Set.mem_image, and_comm]

@[simp] theorem toDivisorDynamics_postcriticalSet
    (hpos : ∀ d, 0 < D.delta d)
    (hsurj : Function.Surjective D.step)
    (hbranch : D.branch.Finite) :
    (D.toDivisorDynamics hpos hsurj hbranch).postcriticalSet = D.postcriticalSet := by
  simp only [DivisorDynamics.postcriticalSet, postcriticalSet,
    D.toDivisorDynamics_branch hpos hsurj hbranch]
  rfl

theorem branch_finite_of_isPCF (h : D.IsPCF) : D.branch.Finite := by
  apply h.subset
  intro d hd
  exact Set.mem_iUnion.mpr ⟨0, ⟨d, hd, rfl⟩⟩

/-- Constant comparison degree cancels from the local tower identity for
`ρh=h_Mρ`. This is the equality of the two dynamical `δ)-indices in
the proof of `lem:pcf-transfer-charp`. -/
theorem delta_eq_of_constant_comparison
    (ρ : Q → P) (q : ℕ) (hq : 0 < q)
    (htower : ∀ d, q * D.delta (ρ d) = E.delta d * q) (d : Q) :
    D.delta (ρ d) = E.delta d := by
  have h := htower d
  rw [mul_comm q] at h
  exact Nat.mul_right_cancel hq h

/-- The commutative comparison square intertwines forward divisor orbits. -/
theorem comparison_iterate
    (ρ : Q → P) (hcomm : ∀ d, ρ (E.step d) = D.step (ρ d))
    (n : ℕ) (d : Q) :
    ρ (E.step^[n] d) = D.step^[n] (ρ d) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hcomm, ih]

/-- A purely inseparable comparison has constant `δ_ρ=q`; the tower
identity and surjectivity then transfer PCF downstairs. The valuation
identity above supplies constancy locally. -/
theorem isPCF_of_constant_comparison
    (ρ : Q → P) (hρ : Function.Surjective ρ)
    (hcomm : ∀ d, ρ (E.step d) = D.step (ρ d))
    (q : ℕ) (hq : 0 < q)
    (htower : ∀ d, q * D.delta (ρ d) = E.delta d * q)
    (hE : E.IsPCF) : D.IsPCF := by
  have hδ (d : Q) : D.delta (ρ d) = E.delta d :=
    D.delta_eq_of_constant_comparison E ρ q hq htower d
  have hbranch : D.branch ⊆ ρ '' E.branch := by
    rintro p ⟨r, hr, rfl⟩
    obtain ⟨d, rfl⟩ := hρ r
    exact ⟨E.step d, ⟨d, by simpa only [critical, Set.mem_ofPred_eq, ← hδ] using hr, rfl⟩,
      hcomm d⟩
  have hpost : D.postcriticalSet ⊆ ρ '' E.postcriticalSet := by
    intro p hp
    obtain ⟨n, r, hr, rfl⟩ := (Set.mem_iUnion.mp hp)
    obtain ⟨d, hd, rfl⟩ := hbranch hr
    refine ⟨E.step^[n] d, ?_, D.comparison_iterate E ρ hcomm n d⟩
    exact Set.mem_iUnion.mpr ⟨n, ⟨d, hd, rfl⟩⟩
  exact (hE.image ρ).subset hpost

/-- The separable-comparison part of `lem:pcf-transfer-charp` at the
weighted divisor level. The finite cover's critical divisor set and the
`δ` tower equality are the geometric inputs. -/
theorem isPCF_of_separable_comparison
    (ρ : Q → P) (hρ : Function.Surjective ρ)
    (hρfib : ∀ p, (ρ ⁻¹' {p}).Finite)
    (hcomm : ∀ d, ρ (E.step d) = D.step (ρ d))
    (δρ : Q → ℕ)
    (hDpos : ∀ d, 0 < D.delta d)
    (hEpos : ∀ d, 0 < E.delta d)
    (hρpos : ∀ d, 0 < δρ d)
    (hDsurj : Function.Surjective D.step)
    (hEsurj : Function.Surjective E.step)
    (hDbranch : D.branch.Finite)
    (hρcritical : {d | 1 < δρ d}.Finite)
    (htower : ∀ d, D.delta (ρ d) * δρ d = δρ (E.step d) * E.delta d)
    (hE : E.IsPCF) : D.IsPCF := by
  have hEbranch := E.branch_finite_of_isPCF hE
  let D' := D.toDivisorDynamics hDpos hDsurj hDbranch
  let E' := E.toDivisorDynamics hEpos hEsurj hEbranch
  let C : DivisorDynamics.RamifiedCover D' E' := {
    map := ρ
    map_surjective := hρ
    finite_fiber := hρfib
    comm := hcomm
    ramificationIdx := δρ
    ramificationIdx_pos := hρpos
    branch_finite := by
      have heq : {p | ∃ d, ρ d = p ∧ 1 < δρ d} = ρ '' {d | 1 < δρ d} := by
        ext p
        simp [Set.mem_image, and_comm]
      rw [heq]
      exact hρcritical.image ρ
    ram_comp := htower
  }
  have hE' : E'.IsPCF := by
    change E.postcriticalSet.Finite at hE
    simpa only [E', DivisorDynamics.IsPCF, E.toDivisorDynamics_postcriticalSet] using hE
  have hD' : D'.IsPCF := C.isPCF hE'
  change D.postcriticalSet.Finite
  simpa only [D', DivisorDynamics.IsPCF, D.toDivisorDynamics_postcriticalSet] using hD'

end DeltaDynamics

#print axioms local_purelyInseparable_delta_eq_finrank
#print axioms isSeparable_of_insepDegree_diamond
#print axioms DeltaDynamics.isPCF_of_constant_comparison
#print axioms DeltaDynamics.isPCF_of_separable_comparison

end Pcf
