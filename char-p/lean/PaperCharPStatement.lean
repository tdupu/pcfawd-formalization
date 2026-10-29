/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Palomar.Statement
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# The Palomar statement surface for `paper-p.tex`, Theorem `thm:A`

Mathlib-vocabulary definitions of the hypotheses and conclusion of Theorem A of
"PCF all the way down in positive characteristic". They build on the shared
definitions of `Pcf.Palomar.Statement` (normalization, normalization lifts,
reduced point closures, iterates). The definitions in the `PaperCharP.Palomar`
namespace below are textually identical to those of `PaperCharPChallenge.lean`;
`PaperCharPBridge` proves that they agree with the development's predicates.
As in `Pcf.Palomar.Statement`, no definition body contains a compound proof term.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

open Pcf.Palomar

namespace PaperCharP.Palomar

noncomputable section

/-! ## The weighted local degree and post-critical finiteness -/

/-- The weighted local degree `δ_f(x) = e_f(x) · [κ(x) : κ(f x)]_insep`: the stalk
ramification index times the inseparable degree of the residue field extension
`κ(f x) → κ(x)` induced by `f`. At a codimension-one point of a normal scheme the first
factor is the ramification index of the extension of discrete valuation rings. -/
def weightedIndexAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : ℕ :=
  letI := (f.residueFieldMap x).hom.toAlgebra
  ramificationIndexAt f x * Field.finInsepDegree (Y.residueField (f x)) (X.residueField x)

/-- The weighted post-critical set of `f : X ⟶ X`: all points `f^[n+1](x)`, `n ≥ 0`, where
`x` is a codimension-one point with `δ_f(x) > 1`. -/
def weightedPostcriticalSet {X : Scheme.{u}} (f : X ⟶ X) : Set X :=
  {y | ∃ x : X, Order.coheight x = 1 ∧ 1 < weightedIndexAt f x ∧
    ∃ n : ℕ, (⇑f)^[n + 1] x = y}

/-- `f` is **PCF** in the normalized weighted sense: for every lift `g` of `f` to the
normalization `ν : X̃ ⟶ X`, the image under `ν` of the weighted post-critical set of `g`
is finite. (`existsUnique_isNormalizationLift` shows there is exactly one such lift.) -/
def IsWeightedNormalizedPCF {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ X) : Prop :=
  ∀ g, IsNormalizationLift f g → (⇑(normalizationMap X) '' weightedPostcriticalSet g).Finite

/-! ## Separability and monodromy of the function-field extension -/

/-- `f` is **generically separable**: the function field `K(X)` (the stalk at the generic
point `η`) is a separable algebra over the stalk at `f η` along the stalk map of `f`. -/
def IsGenericallySeparable {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ X) : Prop :=
  letI := (f.stalkMap (genericPoint X)).hom.toAlgebra
  Algebra.IsSeparable (X.presheaf.stalk (f (genericPoint X))) (X.presheaf.stalk (genericPoint X))

/-- `f` has **monodromy not divisible by `p`**: the stalk `F` at `f η` is a field (as it is
when `f η = η`), the function field `L = K(X)` is a finite separable extension of `F` along
the stalk map of `f`, and the normal (equivalently, Galois) closure of `L / F`, taken inside
an algebraic closure of `L`, has degree over `F` coprime to `p`. -/
def HasPrimeToPMonodromy (p : ℕ) {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ X) : Prop :=
  ∃ hF : IsField (X.presheaf.stalk (f (genericPoint X))),
    letI := hF.toField
    letI := (f.stalkMap (genericPoint X)).hom.toAlgebra
    FiniteDimensional (X.presheaf.stalk (f (genericPoint X)))
        (X.presheaf.stalk (genericPoint X)) ∧
      Algebra.IsSeparable (X.presheaf.stalk (f (genericPoint X)))
        (X.presheaf.stalk (genericPoint X)) ∧
      (Module.finrank (X.presheaf.stalk (f (genericPoint X)))
        (IntermediateField.normalClosure (X.presheaf.stalk (f (genericPoint X)))
          (X.presheaf.stalk (genericPoint X))
          (AlgebraicClosure (X.presheaf.stalk (genericPoint X))))).Coprime p

/-! ## PCF on all subvarieties -/

/-- `f` is **separable and PCF**: generically separable and normalized weighted PCF. -/
def IsSeparablePCF {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ X) : Prop :=
  IsGenericallySeparable f ∧ IsWeightedNormalizedPCF f

/-- **PCF on all subvarieties, to depth `d`.** At depth `0`: `f` is separable and PCF.
At depth `d + 1`: `f` is separable and PCF, and for every point `x` other than the generic
point (the generic point of a proper integral closed subvariety `C`), every `r ≥ 0` and
`q ≥ 1` with `f^[r+q] x = f^[r] x`, every restriction `h` of `f^q` to the reduced closure of
`f^[r] x` (the subvariety `f^r(C)`) is PCF on all subvarieties to depth `d`.
(`exists_pointClosure_restriction` shows such a restriction exists; it is unique because the
closed immersion is a monomorphism.) -/
def IsPCFAllSubvarietiesAtDepth : ℕ → ∀ {X : Scheme.{u}} [IsIntegral X], (X ⟶ X) → Prop
  | 0, _, _, f => IsSeparablePCF f
  | d + 1, X, _, f => IsSeparablePCF f ∧
      ∀ x : X, x ≠ genericPoint X → ∀ r q : ℕ, 1 ≤ q → (⇑f)^[r + q] x = (⇑f)^[r] x →
        ∀ h : pointClosure ((⇑f)^[r] x) ⟶ pointClosure ((⇑f)^[r] x),
          h ≫ pointClosureι ((⇑f)^[r] x) = pointClosureι ((⇑f)^[r] x) ≫ iterateHom f q →
            IsPCFAllSubvarietiesAtDepth d h

/-- **PCF on all subvarieties**: to every finite depth. -/
def IsPCFAllSubvarieties {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ X) : Prop :=
  ∀ d, IsPCFAllSubvarietiesAtDepth d f

end

end PaperCharP.Palomar
