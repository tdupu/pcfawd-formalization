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

/-!
# The Palomar statement surface

A compact restatement, in Mathlib vocabulary, of `Pcf.pcfAllTheWayDown_charZero_unconditional`.
Its definitions are those of the Challenge `PcfChallenge.lean` (beside `Pcf.lean`), and only the module docstring differs.
Every definition here is written so that its body contains no nested proof term that Lean
would abstract into an auxiliary `_proof_n` theorem: each proof obligation is a separately
named lemma applied to variables only.  `Pcf.Palomar.Bridge` proves that these notions agree
with the development's and derives the theorem.
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

/-- The post-critical set of `f : X ⟶ X`: all points `f^[n+1](x)`, `n ≥ 0`, where `x` is a
codimension-one point at which `f` is ramified (`e_f(x) > 1`).  These are the forward images
of the branch divisors of `f`. -/
def postcriticalSet {X : Scheme.{u}} (f : X ⟶ X) : Set X :=
  {y | ∃ x : X, Order.coheight x = 1 ∧ 1 < ramificationIndexAt f x ∧
    ∃ n : ℕ, (⇑f)^[n + 1] x = y}

/-- `f` is **post-critically finite**: its post-critical set is finite, i.e. only finitely
many prime divisors are forward images of branch divisors. -/
def IsPCF {X : Scheme.{u}} (f : X ⟶ X) : Prop :=
  (postcriticalSet f).Finite

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

/-- `f` is **PCF on the normalization**: every lift of `f` to the normalization is PCF.
(`existsUnique_isNormalizationLift` shows there is exactly one such lift.) -/
def IsNormalizedPCF {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ X) : Prop :=
  ∀ g, IsNormalizationLift f g → IsPCF g

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

/-- **PCF all the way down, to depth `d`.** At depth `0`: `f` is PCF on the normalization.
At depth `d + 1`: `f` is PCF on the normalization, and for every point `y` in the forward
orbit of a codimension-one point that is periodic, `f^[p] y = y` with `p ≥ 1`, every
restriction `h` of `f^p` to the reduced closure of `y` is PCF all the way down to depth `d`.
(`exists_pointClosure_restriction` shows such a restriction exists; it is unique because the
closed immersion is a monomorphism.) -/
def PCFAllTheWayDownAtDepth : ℕ → ∀ {X : Scheme.{u}} [IsIntegral X], (X ⟶ X) → Prop
  | 0, _, _, f => IsNormalizedPCF f
  | d + 1, X, _, f => IsNormalizedPCF f ∧
      ∀ y : X, (∃ (x : X) (r : ℕ), Order.coheight x = 1 ∧ (⇑f)^[r] x = y) →
        ∀ p : ℕ, 1 ≤ p → (⇑f)^[p] y = y →
          ∀ h : pointClosure y ⟶ pointClosure y,
            h ≫ pointClosureι y = pointClosureι y ≫ iterateHom f p →
              PCFAllTheWayDownAtDepth d h

/-- **PCF all the way down**: to every finite depth. -/
def PCFAllTheWayDown {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ X) : Prop :=
  ∀ d, PCFAllTheWayDownAtDepth d f

end

end Pcf.Palomar
