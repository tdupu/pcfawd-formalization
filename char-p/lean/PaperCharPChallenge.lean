/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Challenge: `paper-p.tex`, Theorem `thm:A` (PCF on all subvarieties)

This statement surface imports only Mathlib. The `Pcf.Palomar` definitions
(stalk ramification index, normalization and normalization lifts, reduced point
closures, iterates) are copied verbatim from the shared statement surface
`Pcf.Palomar.Statement`; the `PaperCharP.Palomar` definitions are copied verbatim
from `PaperCharPStatement`. Neither copy imports a proof module.

PCF is measured on the normalization with the weighted local degree
`δ = e · [κ : κ']_insep`, and the post-critical divisors are counted on `X`
itself through the normalization map. PCF on all subvarieties requires
separability and PCF at the root, and recursively for every restriction of
`f^q` to the reduced closure of `f^[r] x` whenever `x` is not the generic point
and `f^[r+q] x = f^[r] x` with `q ≥ 1`. Theorem A is selected in two cases:
positive characteristic `p` with monodromy not divisible by `p`, and
characteristic zero with no monodromy premise. The two nonvacuity theorems
guarantee normalization lifts and restrictions exist. No example and no other
result of the manuscript is selected.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf.Palomar

noncomputable section

/-! The scoped instance below only restates a Mathlib instance under a name whose arguments are
variables, so that no definition below contains a compound proof term. -/

/-- Stalks of a scheme are local rings. -/
scoped instance (priority := high) stalk_isLocalRing {X : Scheme.{u}} (x : X) :
    IsLocalRing (X.presheaf.stalk x) :=
  inferInstance

/-! ## Ramification and post-critical finiteness -/

/-- The ramification index `e_f(x)` of `f` at `x`: the ramification index of the maximal
ideal of `𝒪_{X,x}` over the local ring `𝒪_{Y,f(x)}` along the stalk map. At a
codimension-one point of a normal scheme this is the ramification index of the extension of
discrete valuation rings. -/
def ramificationIndexAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : ℕ :=
  letI := (f.stalkMap x).hom.toAlgebra
  (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).ramificationIdx (Y.presheaf.stalk (f x))

/-! ## Normalization -/

/-- The inclusion of the generic point of an integral scheme is quasi-compact. -/
instance genericInclusion_quasiCompact (X : Scheme.{u}) [IsIntegral X] :
    QuasiCompact (X.fromSpecStalk (genericPoint X)) := by
  constructor
  intro U _ _
  have : Unique (PrimeSpectrum X.functionField) := inferInstance
  exact (Set.subsingleton_of_subsingleton (α := PrimeSpectrum X.functionField)).isCompact

/-- The inclusion of the generic point of an integral scheme is quasi-separated. -/
instance genericInclusion_quasiSeparated (X : Scheme.{u}) [IsIntegral X] :
    QuasiSeparated (X.fromSpecStalk (genericPoint X)) := inferInstance

/-- The normalization `X̃` of an integral scheme `X`: Mathlib's relative normalization of `X`
in its function field (the integral closure of `𝒪_X` in `K(X)`). -/
abbrev normalization (X : Scheme.{u}) [IsIntegral X] : Scheme.{u} :=
  (X.fromSpecStalk (genericPoint X)).normalization

/-- The normalization morphism `ν : X̃ ⟶ X`. -/
abbrev normalizationMap (X : Scheme.{u}) [IsIntegral X] : normalization X ⟶ X :=
  (X.fromSpecStalk (genericPoint X)).fromNormalization

/-- The generic point of the normalization, `Spec K(X) ⟶ X̃`. -/
abbrev genericToNormalization (X : Scheme.{u}) [IsIntegral X] :
    Spec (X.presheaf.stalk (genericPoint X)) ⟶ normalization X :=
  (X.fromSpecStalk (genericPoint X)).toNormalization

/-- `g` lifts `f` to the normalization: `ν ∘ g = f ∘ ν`, and `g` maps the generic point of
`X̃` to itself through an endomorphism of `Spec K(X)`. -/
def IsNormalizationLift {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ X)
    (g : normalization X ⟶ normalization X) : Prop :=
  g ≫ normalizationMap X = normalizationMap X ≫ f ∧
    ∃ v : Spec (X.presheaf.stalk (genericPoint X)) ⟶ Spec (X.presheaf.stalk (genericPoint X)),
      genericToNormalization X ≫ g = v ≫ genericToNormalization X

/-! ## Restriction to divisors and the recursion -/

/-- The closure of a point is closed. -/
theorem isClosed_closure_point {X : Scheme.{u}} (y : X) : IsClosed (closure ({y} : Set X)) :=
  isClosed_closure

/-- The reduced closed subscheme `\overline{\{y\}}` of `X`. -/
abbrev pointClosure {X : Scheme.{u}} (y : X) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal ⟨closure {y}, isClosed_closure_point y⟩).subscheme

/-- The closed immersion `\overline{\{y\}} ⟶ X`. -/
abbrev pointClosureι {X : Scheme.{u}} (y : X) : pointClosure y ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal ⟨closure {y}, isClosed_closure_point y⟩).subschemeι

/-- The subscheme cut out by the vanishing ideal of a closed set is reduced. -/
theorem isReduced_vanishingIdeal_subscheme {X : Scheme.{u}} (Z : Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have (U : X.affineOpens) : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) := by
    apply (Ideal.isRadical_iff_quotient_reduced _).mp
    change (PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (Z : Set X))).IsRadical
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  have (U : X.affineOpens) :
      IsReduced (I.subschemeCover.openCover.X U) := by
    change IsReduced (Spec (.of (Γ(X, U) ⧸ I.ideal U)))
    infer_instance
  exact @IsReduced.of_openCover I.subscheme I.subschemeCover.openCover this

/-- The reduced closure of a point is an integral scheme. -/
instance pointClosure_isIntegral {X : Scheme.{u}} (y : X) : IsIntegral (pointClosure y) := by
  have : IsReduced (pointClosure y) :=
    isReduced_vanishingIdeal_subscheme ⟨closure {y}, isClosed_closure_point y⟩
  have : IrreducibleSpace (pointClosure y) :=
    Subtype.irreducibleSpace (isIrreducible_singleton (x := y)).closure
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The `n`-th iterate `f ∘ ⋯ ∘ f` of an endomorphism. -/
def iterateHom {X : Scheme.{u}} (f : X ⟶ X) : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => iterateHom f n ≫ f

end

end Pcf.Palomar

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

/-! ## Selected theorems -/

/-- Theorem A, positive characteristic: a finite dominant normalized weighted PCF
endomorphism with monodromy not divisible by `p` is PCF on all subvarieties. -/
theorem theoremA_positiveCharacteristic
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf : IsWeightedNormalizedPCF f) (hmono : HasPrimeToPMonodromy p f) :
    IsPCFAllSubvarieties f := by
  sorry

/-- Theorem A, characteristic zero: a finite dominant normalized weighted PCF
endomorphism is PCF on all subvarieties. -/
theorem theoremA_characteristicZero
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf : IsWeightedNormalizedPCF f) :
    IsPCFAllSubvarieties f := by
  sorry

/-- The normalization lift quantified over in normalized weighted PCF exists uniquely. -/
theorem existsUnique_isNormalizationLift {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ X)
    [IsFinite f] [IsDominant f] :
    ∃! g : normalization X ⟶ normalization X, IsNormalizationLift f g := by
  sorry

/-- The restriction quantified over in the recursion exists. -/
theorem exists_pointClosure_restriction {X : Scheme.{u}} (F : X ⟶ X) (y : X) (hy : F y = y) :
    ∃ h : pointClosure y ⟶ pointClosure y, h ≫ pointClosureι y = pointClosureι y ≫ F := by
  sorry

end PaperCharP.Palomar
