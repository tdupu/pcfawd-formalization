/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.FactorStabilizerInvariant
public import Pcf.Bounding.AllCodimMonodromy
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# The finite reduced fibre above a centre

For a finite integral closure `B/R` and a centre field `F`, the fibre
`C=B⊗[R]F` is a finite `F`-algebra. Reduction gives the finite reduced
algebra whose field components are used in the all-codimension
monodromy argument of `latex/paper-p.tex`.
-/

@[expose] public section

namespace Pcf

open scoped TensorProduct Pointwise
attribute [local instance] Algebra.TensorProduct.rightAlgebra
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u v w x

variable {R : Type u} {B : Type v} {F : Type w} {G : Type x}
  [CommRing R] [CommRing B] [Field F]
  [Algebra R B] [Algebra R F]
  [Group G]

/-- Finiteness of the tensor fibre of a finite cover. -/
theorem tensorFibre_finiteDimensional
    [Module.Finite R B] : FiniteDimensional F (B ⊗[R] F) := by
  letI : Module.Finite F (F ⊗[R] B) := Module.Finite.base_change R F B
  exact Module.Finite.of_surjective
    (Algebra.TensorProduct.commRight R F B).toLinearMap
    (Algebra.TensorProduct.commRight R F B).surjective

/-- The nilradical quotient of the tensor fibre is reduced. -/
theorem tensorFibre_reduced_quotient_isReduced :
    IsReduced ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) := by
  exact (Ideal.isRadical_iff_quotient_reduced _).mp
    (Ideal.radical_isRadical (0 : Ideal (B ⊗[R] F)))

/-- The reduced fibre remains finite-dimensional over the centre's
function field. -/
theorem tensorFibre_reduced_quotient_finiteDimensional
    [Module.Finite R B] :
    FiniteDimensional F
      ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) := by
  letI : FiniteDimensional F (B ⊗[R] F) := tensorFibre_finiteDimensional
  exact Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ F (nilradical (B ⊗[R] F))).toLinearMap
    (Ideal.Quotient.mkₐ_surjective F _)

#print axioms tensorFibre_finiteDimensional
#print axioms tensorFibre_reduced_quotient_isReduced
#print axioms tensorFibre_reduced_quotient_finiteDimensional

section GroupAction

variable [MulSemiringAction G B] [SMulCommClass G R B]

/-- The Galois action on the first factor induces automorphisms of
the tensor fibre. -/
def tensorFibreActionHom : G →* (B ⊗[R] F ≃ₐ[R] B ⊗[R] F) where
  toFun g := Algebra.TensorProduct.congr
    ((MulSemiringAction.toAlgAut G R B) g) AlgEquiv.refl
  map_one' := by
    change Algebra.TensorProduct.congr
      ((MulSemiringAction.toAlgAut G R B) 1) AlgEquiv.refl = 1
    rw [map_one]
    exact Algebra.TensorProduct.congr_refl
  map_mul' g h := by
    apply AlgEquiv.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul b a =>
      simp [Algebra.TensorProduct.congr_apply,
        Algebra.TensorProduct.map_tmul, mul_smul]
    | add z₁ z₂ h₁ h₂ =>
      simp only [map_add, h₁, h₂]

/-- Canonical semiring action on the tensor fibre. -/
@[instance_reducible] def tensorFibreMulSemiringAction : MulSemiringAction G (B ⊗[R] F) :=
  MulSemiringAction.compHom _ (tensorFibreActionHom (R := R) (B := B) (F := F) (G := G))

attribute [local instance] tensorFibreMulSemiringAction

@[simp] theorem tensorFibre_smul_tmul
    (g : G) (b : B) (a : F) :
    g • (b ⊗ₜ[R] a) = (g • b) ⊗ₜ[R] a := by
  change (Algebra.TensorProduct.congr
    ((MulSemiringAction.toAlgAut G R B) g) AlgEquiv.refl) (b ⊗ₜ[R] a) = _
  simp [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]

/-- The base-field scalars in the second tensor factor are fixed. -/
theorem tensorFibre_smul_scalar (g : G) (a : F) :
    g • algebraMap F (B ⊗[R] F) a = algebraMap F (B ⊗[R] F) a := by
  change g • (1 ⊗ₜ[R] a) = 1 ⊗ₜ[R] a
  simp only [tensorFibre_smul_tmul, smul_one]

/-- The tensor action is linear over the centre field. -/
theorem tensorFibreSmulCommClass : SMulCommClass G F (B ⊗[R] F) := by
  refine ⟨fun g a z => ?_⟩
  change g • (algebraMap F (B ⊗[R] F) a * z) =
    algebraMap F (B ⊗[R] F) a * (g • z)
  rw [smul_mul', tensorFibre_smul_scalar]

attribute [local instance] tensorFibreSmulCommClass

/-- The tensor action agrees with the base-changed linear
representation used by Reynolds averaging. -/
theorem tensorFibre_smul_eq_representation
    (g : G) (z : B ⊗[R] F) :
    g • z = (tensorBaseChangeRepresentation (F := F)
      (ringActionRepresentation (R := R) (B := B) (G := G))) g z := by
  induction z using TensorProduct.inductionOn with
  | tmul b a =>
    simp only [tensorFibre_smul_tmul,
      tensorBaseChangeRepresentation_tmul, ringActionRepresentation_apply]
  | add z₁ z₂ h₁ h₂ =>
    change (tensorFibreActionHom (R := R) (B := B) (F := F) (G := G) g)
      (z₁ + z₂) = _
    rw [map_add, map_add]
    exact congrArg₂ (· + ·) h₁ h₂

/-- The nilradical is stable under every automorphism of the tensor
fibre, so reduction carries the Galois action. -/
theorem tensorFibre_nilradical_stable
    (g : G) (z : B ⊗[R] F)
    (hz : z ∈ nilradical (B ⊗[R] F)) :
    g • z ∈ nilradical (B ⊗[R] F) := by
  obtain ⟨n, hn⟩ := (mem_nilradical).mp hz
  apply (mem_nilradical).mpr
  refine ⟨n, ?_⟩
  change ((tensorFibreActionHom (R := R) (B := B) (F := F) (G := G) g) z) ^ n = 0
  rw [← map_pow, hn, map_zero]

/-- The nilradical is fixed as an ideal by the tensor action. -/
theorem tensorFibre_nilradical_smul_eq (g : G) :
    g • nilradical (B ⊗[R] F) = nilradical (B ⊗[R] F) := by
  ext z
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · intro hz
    have h := tensorFibre_nilradical_stable (R := R) (B := B) (F := F)
      g (g⁻¹ • z) hz
    simpa only [smul_inv_smul] using h
  · intro hz
    exact tensorFibre_nilradical_stable (R := R) (B := B) (F := F)
      g⁻¹ z hz

/-- Every group element belongs to the stabilizer of the nilradical. -/
def tensorFibre_nilradicalStabilizerHom :
    G →* MulAction.stabilizer G (nilradical (B ⊗[R] F)) where
  toFun g := ⟨g, tensorFibre_nilradical_smul_eq (R := R) (B := B) (F := F) g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Action induced on the actual reduced fibre quotient ring. -/
def tensorFibreReducedActionHom :
    G →* (((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) ≃ₐ[
      F ⧸ (nilradical (B ⊗[R] F)).under F]
      ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F))) :=
  (Ideal.Quotient.stabilizerHom (nilradical (B ⊗[R] F))
    ((nilradical (B ⊗[R] F)).under F) G).comp
      (tensorFibre_nilradicalStabilizerHom (R := R) (B := B) (F := F) (G := G))

@[instance_reducible] def tensorFibreReducedAction :
    MulSemiringAction G
      ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) :=
  MulSemiringAction.compHom _
    (tensorFibreReducedActionHom (R := R) (B := B) (F := F) (G := G))

attribute [local instance] tensorFibreReducedAction

@[simp] theorem tensorFibreReduced_smul_mk
    (g : G) (z : B ⊗[R] F) :
    g • Ideal.Quotient.mk (nilradical (B ⊗[R] F)) z =
      Ideal.Quotient.mk (nilradical (B ⊗[R] F)) (g • z) := by
  change (Ideal.Quotient.stabilizerHom
    (nilradical (B ⊗[R] F))
    ((nilradical (B ⊗[R] F)).under F) G
    ⟨g, tensorFibre_nilradical_smul_eq (R := R) (B := B) (F := F) g⟩)
      (Ideal.Quotient.mk (nilradical (B ⊗[R] F)) z) = _
  simp only [Ideal.Quotient.stabilizerHom_apply,
    MulAction.subgroup_smul_def]

/-- The induced action fixes the base-field scalars of the reduced
fibre. -/
theorem tensorFibreReduced_smul_scalar (g : G) (a : F) :
    g • algebraMap F
      ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) a =
      algebraMap F ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) a := by
  change g • Ideal.Quotient.mk (nilradical (B ⊗[R] F))
    (algebraMap F (B ⊗[R] F) a) = _
  rw [tensorFibreReduced_smul_mk, tensorFibre_smul_scalar]
  exact Ideal.Quotient.mk_algebraMap F _ a

/-- The reduced-fibre action is linear over the centre field. -/
theorem tensorFibreReducedSmulCommClass :
    SMulCommClass G F
      ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) := by
  refine ⟨fun g a z => ?_⟩
  change g • (algebraMap F _ a * z) = algebraMap F _ a * (g • z)
  rw [smul_mul', tensorFibreReduced_smul_scalar]

attribute [local instance] tensorFibreReducedSmulCommClass

section FiniteGroup

variable [Fintype G]

/-- Reynolds averaging shows that a fixed class of the actual reduced
tensor fibre is a scalar. Fixedness is expressed on lifts; it is
precisely fixedness for the induced quotient action. -/
theorem tensorFibre_reduced_fixed_is_scalar
    [Algebra.IsInvariant R B G] [Invertible (Fintype.card G : R)]
    (x : (B ⊗[R] F) ⧸ nilradical (B ⊗[R] F))
    (hx : ∀ (g : G) (z : B ⊗[R] F),
      Ideal.Quotient.mk (nilradical (B ⊗[R] F)) z = x →
      Ideal.Quotient.mk (nilradical (B ⊗[R] F))
        ((tensorBaseChangeRepresentation (F := F)
          (ringActionRepresentation (R := R) (B := B) (G := G))) g z) = x) :
    ∃ a : F, algebraMap F
      ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) a = x := by
  let C := B ⊗[R] F
  let I := nilradical C
  let ρ := tensorBaseChangeRepresentation (F := F)
    (ringActionRepresentation (R := R) (B := B) (G := G))
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a, ha⟩ := tensorBaseChange_invariant_is_scalar
    (F := F) (ringActionRepresentation (R := R) (B := B) (G := G))
    (fun b hb => Algebra.IsInvariant.isInvariant (G := G) b (fun g => hb g))
    (ρ.averageMap z) (ρ.averageMap_invariant z)
  refine ⟨a, ?_⟩
  have havg : ρ.averageMap z =
      ⅟(Fintype.card G : R) • ∑ g : G, ρ g z := by
    simp [ρ, Representation.averageMap, GroupAlgebra.average]
  have hq : (Ideal.Quotient.mkₐ R I) (ρ.averageMap z) =
      Ideal.Quotient.mk I z := by
    rw [havg, map_smul, map_sum]
    simp_rw [show ∀ g : G,
      (Ideal.Quotient.mkₐ R I) (ρ g z) = Ideal.Quotient.mk I z from
      fun g => hx g z rfl]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcast : ((Fintype.card G : ℕ) : C ⧸ I) * Ideal.Quotient.mk I z =
        (Fintype.card G : R) • Ideal.Quotient.mk I z := by
      simp [Algebra.smul_def]
    rw [hcast]
    rw [smul_smul, invOf_mul_self, one_smul]
  rw [← ha] at hq
  exact hq

/-- The invariant ring of the actual reduced tensor fibre is the
centre field. This packages Reynolds exactness as the same
`Algebra.IsInvariant` instance used by the field-factor theorem. -/
theorem tensorFibreReduced_isInvariant
    [Algebra.IsInvariant R B G] [Invertible (Fintype.card G : R)] :
    Algebra.IsInvariant F
      ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) G := by
  refine ⟨fun x hx => ?_⟩
  apply tensorFibre_reduced_fixed_is_scalar (R := R) (B := B) (G := G) x
  intro g z hz
  calc
    Ideal.Quotient.mk (nilradical (B ⊗[R] F))
        ((tensorBaseChangeRepresentation (F := F)
          (ringActionRepresentation (R := R) (B := B) (G := G))) g z) =
      Ideal.Quotient.mk (nilradical (B ⊗[R] F)) (g • z) := by
        rw [tensorFibre_smul_eq_representation]
    _ = g • Ideal.Quotient.mk (nilradical (B ⊗[R] F)) z :=
      (tensorFibreReduced_smul_mk (R := R) (B := B) (F := F) g z).symm
    _ = g • x := congrArg (g • ·) hz
    _ = x := hx g

attribute [local instance] tensorFibreReduced_isInvariant

/-- Characteristic-`p` form of the invariant-ring calculation. -/
theorem tensorFibreReduced_isInvariant_charP
    (p : ℕ) (hp : p.Prime) [CharP R p]
    [Algebra.IsInvariant R B G]
    (horder : (Fintype.card G).Coprime p) :
    Algebra.IsInvariant F
      ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) G := by
  letI : Invertible (Fintype.card G : R) :=
    ((nonempty_invertible_iff_isUnit _).mpr
      ((CharP.isUnit_natCast_iff hp).mpr
        (hp.coprime_iff_not_dvd.mp horder.symm))).some
  exact tensorFibreReduced_isInvariant (R := R) (B := B) (F := F) (G := G)

/-- Each actual field component of the finite reduced tensor fibre
has fixed field `F` under its stabilizer. -/
theorem tensorFibre_factor_stabilizer_fixed_set_eq_range
    (p : ℕ) (hp : p.Prime) [CharP R p] [CharP F p]
    [Module.Finite R B] [Algebra.IsInvariant R B G]
    (horder : (Fintype.card G).Coprime p)
    (m : MaximalSpectrum
      ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F))) :
    {x : ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) ⧸ m.asIdeal |
      ∀ g : MulAction.stabilizer G m.asIdeal,
        Ideal.Quotient.stabilizerHom m.asIdeal (⊥ : Ideal F) G g x = x} =
      Set.range (algebraMap F
        (((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) ⧸ m.asIdeal)) := by
  letI : FiniteDimensional F
      ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) :=
    tensorFibre_reduced_quotient_finiteDimensional
  letI : IsReduced
      ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) :=
    tensorFibre_reduced_quotient_isReduced
  letI : Algebra.IsInvariant F
      ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) G :=
    tensorFibreReduced_isInvariant_charP p hp horder
  exact reducedFactor_stabilizerHom_fixed_set_eq_range
    (F := F) p hp horder m

/-- All components of the actual reduced tensor fibre form one
Galois orbit, because its invariant ring is the centre field. -/
theorem tensorFibre_reduced_factors_transitive
    (p : ℕ) (hp : p.Prime) [CharP R p]
    [Module.Finite R B] [Algebra.IsInvariant R B G]
    (horder : (Fintype.card G).Coprime p)
    (m n : MaximalSpectrum
      ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F))) :
    ∃ g : G, n.asIdeal = g • m.asIdeal := by
  letI : FiniteDimensional F
      ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) :=
    tensorFibre_reduced_quotient_finiteDimensional
  letI : IsReduced
      ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) :=
    tensorFibre_reduced_quotient_isReduced
  letI : Algebra.IsInvariant F
      ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) G :=
    tensorFibreReduced_isInvariant_charP p hp horder
  exact reducedFiniteAlgebra_factors_transitive
    (F := F) (G := G) m n

/-- The actual Galois stabilizer acts on the field component of the
reduced fibre. -/
@[instance_reducible] def tensorFibreFactorStabilizerAction
    (m : MaximalSpectrum
      ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F))) :
    MulSemiringAction (MulAction.stabilizer G m.asIdeal)
      (((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) ⧸ m.asIdeal) :=
  MulSemiringAction.compHom _
    (Ideal.Quotient.stabilizerHom m.asIdeal (⊥ : Ideal F) G)

omit [Fintype G] in
/-- The field-component stabilizer fixes the base field pointwise. -/
theorem tensorFibreFactorStabilizerSmulCommClass
    (m : MaximalSpectrum
      ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F))) :
    letI := tensorFibreFactorStabilizerAction (R := R) (B := B) (F := F) (G := G) m
    SMulCommClass (MulAction.stabilizer G m.asIdeal) F
      (((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) ⧸ m.asIdeal) := by
  letI := tensorFibreFactorStabilizerAction (R := R) (B := B) (F := F) (G := G) m
  refine ⟨fun g c x => ?_⟩
  change (Ideal.Quotient.stabilizerHom m.asIdeal (⊥ : Ideal F) G g)
    (algebraMap F _ c * x) = algebraMap F _ c *
      (Ideal.Quotient.stabilizerHom m.asIdeal (⊥ : Ideal F) G g) x
  rw [map_mul]
  congr 1
  have h := (Ideal.Quotient.stabilizerHom m.asIdeal (⊥ : Ideal F) G g).commutes
    (Ideal.Quotient.mk (⊥ : Ideal F) c)
  simpa only [Ideal.Quotient.algebraMap_mk_of_liesOver,
    Ideal.Quotient.mk_algebraMap] using h

/-- The fixed field of the genuine factor-stabilizer action is `F`. -/
theorem tensorFibreFactorStabilizer_isInvariant
    (p : ℕ) (hp : p.Prime) [CharP R p] [CharP F p]
    [Module.Finite R B] [Algebra.IsInvariant R B G]
    (horder : (Fintype.card G).Coprime p)
    (m : MaximalSpectrum
      ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F))) :
    letI := tensorFibreFactorStabilizerAction (R := R) (B := B) (F := F) (G := G) m
    Algebra.IsInvariant F
      (((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) ⧸ m.asIdeal)
      (MulAction.stabilizer G m.asIdeal) := by
  letI := tensorFibreFactorStabilizerAction (R := R) (B := B) (F := F) (G := G) m
  refine ⟨fun x hx => ?_⟩
  have hset := tensorFibre_factor_stabilizer_fixed_set_eq_range
    (R := R) (B := B) (F := F) (G := G) p hp horder m
  exact (Set.ext_iff.mp hset x).mp hx

/-- Each field component of the specialized finite Galois cover has
prime-to-`p` monodromy over the centre field. -/
theorem tensorFibre_factor_primeToPMonodromy
    (p : ℕ) (hp : p.Prime) [CharP R p] [CharP F p]
    [Module.Finite R B] [Algebra.IsInvariant R B G]
    (horder : (Fintype.card G).Coprime p)
    (m : MaximalSpectrum
      ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F))) :
    letI : Field
      (((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) ⧸ m.asIdeal) :=
      Ideal.Quotient.field m.asIdeal
    IsPrimeToPMonodromy.{w, max v w, max v w} p F
      (((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) ⧸ m.asIdeal) := by
  let L := ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) ⧸ m.asIdeal
  let H := MulAction.stabilizer G m.asIdeal
  letI : Field L := Ideal.Quotient.field m.asIdeal
  letI : MulSemiringAction H L :=
    tensorFibreFactorStabilizerAction (R := R) (B := B) (F := F) (G := G) m
  letI : SMulCommClass H F L :=
    tensorFibreFactorStabilizerSmulCommClass (R := R) (B := B) (F := F) (G := G) m
  letI : Algebra.IsInvariant F L H :=
    tensorFibreFactorStabilizer_isInvariant
      (R := R) (B := B) (F := F) (G := G) p hp horder m
  have hH : (Fintype.card H).Coprime p :=
    Nat.Coprime.of_dvd_left
      (by simpa only [Nat.card_eq_fintype_card] using H.card_subgroup_dvd_card)
      horder
  exact isPrimeToPMonodromy_of_fixed_field p F L H hH

#print axioms tensorFibre_nilradical_stable
#print axioms tensorFibreReduced_isInvariant
#print axioms tensorFibreReduced_isInvariant_charP
#print axioms tensorFibre_factor_stabilizer_fixed_set_eq_range
#print axioms tensorFibre_reduced_factors_transitive
#print axioms tensorFibre_factor_primeToPMonodromy

end FiniteGroup

end GroupAction

end Pcf
