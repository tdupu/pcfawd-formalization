/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.TheoremAWeightedDownstairs

/-!
# PCF all the way down on divisors, in every characteristic

`latex/paper-p.tex`, Definition `def:pcfawd`, is the divisorial recursion:
`f` is PCF, and for every preperiodic integral effective divisor `A` with
`f^{r+s}(A) = f^r(A)` the return `f^s` on `f^r(A)` is again PCF all the way
down. `IsPCFAllDivisors` states it with the same PCF predicate, return maps and
original reduced subvarieties as `IsPCFAllSubvarieties`, but quantifying only
over codimension-one points. Since a codimension-one point is a proper
subvariety, the all-subvariety property implies it. This gives Corollary
`cor:charp-pcfawd` in characteristic `p` and the divisorial form of
`cor:pcfawd` in characteristic zero.
-/

@[expose] public section

universe u

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

/-- `paper-p.tex`, Definition `def:pcfawd`, through `d` recursive divisor
returns.

`paper-p.tex` correspondence: Definition 3.3 (`def:pcfawd`). -/
def IsPCFAllDivisorsAtDepth
    (k : Type u) [Field k]
    (d : ℕ) {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] : Prop :=
  match d with
  | 0 => IsSeparableNormalizedPCF k s f
  | d + 1 =>
      IsSeparableNormalizedPCF k s f ∧
        ∀ (C : SchemeDivisorPoint X) (r p : ℕ) (_hp : 1 ≤ p)
          (hperiodic : schemePointIterate f (r + p) C.1 = schemePointIterate f r C.1),
          IsPCFAllDivisorsAtDepth k d
            ((pointClosureIdealSheaf (schemePointIterate f r C.1)).subschemeι ≫ s)
            (eventuallyPeriodicPointReturn f r p C.1 hperiodic)

/-- **PCF all the way down** (`paper-p.tex`, Definition `def:pcfawd`), on the
original reduced divisors, to every depth.

`paper-p.tex` correspondence: Definition 3.3 (`def:pcfawd`). -/
def IsPCFAllDivisors
    (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] : Prop :=
  ∀ d, IsPCFAllDivisorsAtDepth k d s f

/-- A codimension-one point of an integral scheme is not its generic point. -/
theorem SchemeDivisorPoint.ne_genericPoint {X : Scheme.{u}} [IsIntegral X]
    (C : SchemeDivisorPoint X) : C.1 ≠ genericPoint X := by
  intro h
  have hmax : IsMax C.1 := by
    intro y _
    rw [h]
    exact (genericPoint_spec X).specializes (Set.mem_univ y)
  have h0 : Order.coheight C.1 = 0 := Order.coheight_eq_zero.mpr hmax
  have h1 : Order.coheight C.1 = 1 := C.2
  rw [h0] at h1
  exact zero_ne_one h1

/-- The all-subvariety recursion implies the divisorial one, depth by depth. -/
theorem IsPCFAllSubvarietiesAtDepth.isPCFAllDivisorsAtDepth
    (k : Type u) [Field k] (d : ℕ) :
    ∀ {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
      (f : X ⟶ X) [IsFinite f] [IsDominant f]
      [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X],
      IsPCFAllSubvarietiesAtDepth k d s f → IsPCFAllDivisorsAtDepth k d s f := by
  induction d with
  | zero => intro X s _ f _ _ _ _ _ h; exact h
  | succ d ih =>
      intro X s _ f _ _ _ _ _ h
      exact ⟨h.1, fun C r p hp hperiodic =>
        ih _ _ (h.2 ⟨C.1, C.ne_genericPoint⟩ r p hp hperiodic)⟩

/-- PCF on all subvarieties implies PCF all the way down on divisors. -/
theorem IsPCFAllSubvarieties.isPCFAllDivisors
    (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (h : IsPCFAllSubvarieties k s f) : IsPCFAllDivisors k s f :=
  fun d => IsPCFAllSubvarietiesAtDepth.isPCFAllDivisorsAtDepth k d s f (h d)

/-- **PCF all the way down in characteristic zero** (`paper-p.tex`,
`cor:pcfawd`), on the original reduced divisors, from the paper's PCF
hypothesis.

`paper-p.tex` correspondence: Conjecture 3.4 (`conj:pcfawd`), Corollary 9.6 (`cor:pcfawd`). -/
theorem isPCFAllDivisors_charZero_of_downstairsPCF
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf : IsWeightedNormalizedPCFDownstairs k s f) :
    IsPCFAllDivisors k s f :=
  IsPCFAllSubvarieties.isPCFAllDivisors k s f
    (isPCFAllSubvarieties_charZero_of_downstairsPCF k s f hpcf)

/-- **PCF all the way down in characteristic `p`** (`paper-p.tex`,
`cor:charp-pcfawd`), on the original reduced divisors, from the paper's PCF
hypothesis and prime-to-`p` monodromy.

`paper-p.tex` correspondence: Corollary 9.6 (`cor:pcfawd`). -/
theorem isPCFAllDivisors_charP_of_downstairsPCF
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf : IsWeightedNormalizedPCFDownstairs k s f)
    (hmono : IsPrimeToPMonodromyMap p f) :
    IsPCFAllDivisors k s f :=
  IsPCFAllSubvarieties.isPCFAllDivisors k s f
    (isPCFAllSubvarieties_charP_of_downstairsPCF p hp k s f hpcf hmono)

#print axioms IsPCFAllSubvarieties.isPCFAllDivisors
#print axioms isPCFAllDivisors_charZero_of_downstairsPCF
#print axioms isPCFAllDivisors_charP_of_downstairsPCF

end

end Pcf
