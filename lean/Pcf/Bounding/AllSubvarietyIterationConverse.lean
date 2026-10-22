/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllSubvarietyIterationRecursive

/-!
# Converse recursive iteration invariance

For a finite self-map, the image of a proper integral point closure remains
proper. Hence an eventual return for `f` can be tested at its periodic image
as a return for `f^m`; that return is the `m`-th power of the original one.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-- A finite dominant self-map of an integral scheme cannot send a
non-generic point to the generic point. The key fact is that finite fibres
are discrete, while the ambient generic point specializes to every point. -/
theorem finiteDominant_map_properPoint
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (x : X) (hx : x ≠ genericPoint X) : f x ≠ genericPoint X := by
  intro hfx
  have hη : f (genericPoint X) = genericPoint X :=
    map_genericPoint_eq_of_isDominant f
  have hdisc := f.isDiscrete_preimage_singleton (genericPoint X)
  have hmemη : genericPoint X ∈ f ⁻¹' {genericPoint X} := by
    simpa using hη
  have hmemx : x ∈ f ⁻¹' {genericPoint X} := by
    simpa using hfx
  have heq := hdisc.eq_of_specializes (genericPoint_specializes x) hmemη hmemx
  exact hx heq.symm

/-- The eventually periodic image of a proper integral centre is again a
proper integral centre, including when the preperiod is zero. -/
theorem properIntegralSubvarietyPoint_iterate
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (C : ProperIntegralSubvarietyPoint X) (r : ℕ) :
    schemePointIterate f r C.1 ≠ genericPoint X := by
  let g := (End.of f ^ r).asHom
  change g C.1 ≠ genericPoint X
  exact finiteDominant_map_properPoint g C.1 C.2

/-- The recursive all-subvariety property descends from a positive
iterate. At each return, test the periodic image as a proper centre for
the ambient iterate and invoke induction on the actual return morphism. -/
theorem isPCFAllSubvarietiesAtDepth_of_pow
    (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (m : ℕ) (hm : 1 ≤ m) (d : ℕ)
    (h : IsPCFAllSubvarietiesAtDepth k d s (End.of f ^ m).asHom) :
    IsPCFAllSubvarietiesAtDepth k d s f := by
  induction d generalizing X s f with
  | zero =>
      exact (isSeparableNormalizedPCF_pow_iff k s f m hm).1 h
  | succ d ih =>
      refine ⟨(isSeparableNormalizedPCF_pow_iff k s f m hm).1 h.1, ?_⟩
      intro C r p hp hperiodic
      let B : ProperIntegralSubvarietyPoint X :=
        ⟨schemePointIterate f r C.1,
          properIntegralSubvarietyPoint_iterate f C r⟩
      have hperiodicB : schemePointIterate (End.of f ^ m).asHom (0 + p) B.1 =
          schemePointIterate (End.of f ^ m).asHom 0 B.1 := by
        simpa [B, schemePointIterate] using
          schemePointIterate_periodic_for_ambient_pow f r p m C.1 hperiodic
      have hBpow := h.2 B 0 p hp hperiodicB
      have hreturn :=
        eventuallyPeriodicPointReturn_pow_on_image f r p m C.1 hperiodic
      have hreturnB :
          (End.of (eventuallyPeriodicPointReturn f r p C.1 hperiodic) ^ m).asHom =
          eventuallyPeriodicPointReturn (End.of f ^ m).asHom 0 p B.1
            hperiodicB := by
        exact hreturn
      apply ih
      have hBpow' : IsPCFAllSubvarietiesAtDepth k d
          ((pointClosureIdealSheaf B.1).subschemeι ≫ s)
          (eventuallyPeriodicPointReturn (End.of f ^ m).asHom 0 p B.1
            hperiodicB) := by
        have hzero : schemePointIterate (End.of f ^ m).asHom 0 B.1 = B.1 := by
          simp [schemePointIterate]
        exact Eq.mp (by cases hzero; rfl) hBpow
      simpa only [hreturnB] using hBpow'

/-- `paper-p.tex`, Lemma `lem:allsubvar-iterate`, for the actual recursive
all-subvariety predicate and every positive iterate. -/
theorem isPCFAllSubvarieties_pow_iff
    (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (m : ℕ) (hm : 1 ≤ m) :
    IsPCFAllSubvarieties k s (End.of f ^ m).asHom ↔
      IsPCFAllSubvarieties k s f := by
  constructor
  · intro h d
    exact isPCFAllSubvarietiesAtDepth_of_pow k s f m hm d (h d)
  · exact isPCFAllSubvarieties_pow_of k s f m hm

#print axioms finiteDominant_map_properPoint
#print axioms properIntegralSubvarietyPoint_iterate
#print axioms isPCFAllSubvarietiesAtDepth_of_pow
#print axioms isPCFAllSubvarieties_pow_iff

end Pcf
