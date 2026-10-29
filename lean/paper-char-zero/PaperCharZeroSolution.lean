/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import main
public import Pcf.Palomar.Bridge

/-!
# Solution: characteristic-zero paper headline statements

The two headline bridges use the actual paper-facing proofs in `main`.
`Pcf.Palomar.Bridge` proves equivalence of the independently described normalized
PCF and divisor recursion with the library objects; its point-closure transport
identifies the arbitrary restriction with the actual reduced-image return.
This module does not import the Challenge or its statement placeholders.
-/

@[expose] public section

universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace

open Pcf.Palomar

namespace PaperCharZero.Palomar

/-- Theorem A: every return on a preperiodic integral effective divisor is PCF. -/
theorem theoremA
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (hpcf : IsNormalizedPCF f)
    (y : X) (hy : ∃ (x : X) (r : ℕ), Order.coheight x = 1 ∧ (⇑f)^[r] x = y)
    (p : ℕ) (hp : 1 ≤ p) (hper : (⇑f)^[p] y = y)
    (g : pointClosure y ⟶ pointClosure y)
    (hg : g ≫ pointClosureι y = pointClosureι y ≫ iterateHom f p) :
    IsNormalizedPCF g := by
  have hscheme := (Pcf.Palomar.isNormalizedPCF_iff_scheme k s f).mp hpcf
  have hdepth : Pcf.SchemePCFAllTheWayDownAtDepth k 1 s f := by
    refine ⟨hscheme, ?_⟩
    intro A r q hq hA
    exact PaperCharZero.theoremA k s f A r q hq hA hscheme
  exact (Pcf.Palomar.pcfAllTheWayDownAtDepth_of_scheme k 1 s f hdepth).2
    y hy p hp hper g hg

/-- Corollary: normalized PCF holds through every finite divisor descent. -/
theorem cor_pcfawd
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (hpcf : IsNormalizedPCF f) : PCFAllTheWayDown f := by
  apply (Pcf.Palomar.pcfAllTheWayDown_iff_scheme k s f).mpr
  exact PaperCharZero.cor_pcfawd k s f
    ((Pcf.Palomar.isNormalizedPCF_iff_scheme k s f).mp hpcf)

/-- The normalization lift quantified over in normalized PCF exists uniquely. -/
theorem existsUnique_isNormalizationLift {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ X)
    [IsFinite f] [IsDominant f] :
    ∃! g : normalization X ⟶ normalization X, IsNormalizationLift f g := by
  exact Pcf.Palomar.existsUnique_isNormalizationLift f

/-- The restriction quantified over in Theorem A and the recursion exists. -/
theorem exists_pointClosure_restriction {X : Scheme.{u}} (F : X ⟶ X) (y : X) (hy : F y = y) :
    ∃ h : pointClosure y ⟶ pointClosure y, h ≫ pointClosureι y = pointClosureι y ≫ F := by
  exact Pcf.Palomar.exists_pointClosure_restriction F y hy

#check @theoremA
#check @cor_pcfawd
#print axioms theoremA
#print axioms cor_pcfawd
#print axioms existsUnique_isNormalizationLift
#print axioms exists_pointClosure_restriction

end PaperCharZero.Palomar
