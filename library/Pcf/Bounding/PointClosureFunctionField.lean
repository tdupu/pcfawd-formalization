/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeAllCentreMonodromy
public import Pcf.Bounding.RegularLocus
public import Pcf.Bounding.SchemeBridge

/-!
# Function fields of reduced point closures

The generic stalk field of the reduced closure of a point is the
fraction field of its quotient coordinate ring on every affine
neighborhood. This identifies the fields in the affine all-centre
monodromy theorem with the function fields of the actual geometric
centres.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry TopologicalSpace

universe u

set_option linter.style.haveILetI false

/-- The generic stalk of the reduced point closure is the fraction
field of its quotient affine coordinate ring. -/
theorem pointClosure_functionField_isFractionRing
    {X : Scheme.{u}} (x : X)
    (U : X.affineOpens) (hx : x ∈ (U : X.Opens)) :
    let I := pointClosureIdealSheaf x
    let hmem : genericPoint I.subscheme ∈
        I.subschemeι ⁻¹ᵁ (U : X.Opens) := by
      change I.subschemeι (genericPoint I.subscheme) ∈ (U : X.Opens)
      rw [pointClosureSubschemeι_genericPoint]
      exact hx
    letI : Algebra (Γ(X, U) ⧸ I.ideal U)
        I.subscheme.functionField :=
      I.quotientStalkAlgebra U (genericPoint I.subscheme) hmem
    IsFractionRing (Γ(X, U) ⧸ I.ideal U)
      I.subscheme.functionField := by
  let I := pointClosureIdealSheaf x
  let W : I.subscheme.Opens := I.subschemeι ⁻¹ᵁ (U : X.Opens)
  have hmem : genericPoint I.subscheme ∈ W := by
    change I.subschemeι (genericPoint I.subscheme) ∈ (U : X.Opens)
    rw [pointClosureSubschemeι_genericPoint]
    exact hx
  letI : Nonempty W := ⟨⟨genericPoint I.subscheme, hmem⟩⟩
  let hW : IsAffineOpen W := by
    letI : IsOpenImmersion (I.subschemeCover.f U) := I.subschemeCover.map_prop U
    dsimp only [W]
    rw [← I.opensRange_subschemeCover_map U]
    exact isAffineOpen_opensRange (I.subschemeCover.f U)
  let e : (Γ(X, U) ⧸ I.ideal U) ≃+* Γ(I.subscheme, W) :=
    (I.subschemeObjIso U).symm.commRingCatIsoToRingEquiv
  letI : Algebra Γ(I.subscheme, W) I.subscheme.functionField :=
    TopCat.Presheaf.algebra_section_stalk I.subscheme.presheaf
      ⟨genericPoint I.subscheme, hmem⟩
  letI : IsFractionRing Γ(I.subscheme, W) I.subscheme.functionField :=
    functionField_isFractionRing_of_isAffineOpen I.subscheme W hW
  letI : Algebra (Γ(X, U) ⧸ I.ideal U) I.subscheme.functionField :=
    I.quotientStalkAlgebra U (genericPoint I.subscheme) hmem
  exact IsFractionRing.of_ringEquiv_left e (by intro r; rfl)

/-- The canonical quotient fraction field is isomorphic to the
geometric generic stalk field of the reduced point closure. -/
noncomputable def pointClosure_fractionRingAlgEquiv
    {X : Scheme.{u}} (x : X)
    (U : X.affineOpens) (hx : x ∈ (U : X.Opens)) :
    let I := pointClosureIdealSheaf x
    let hmem : genericPoint I.subscheme ∈
        I.subschemeι ⁻¹ᵁ (U : X.Opens) := by
      change I.subschemeι (genericPoint I.subscheme) ∈ (U : X.Opens)
      rw [pointClosureSubschemeι_genericPoint]
      exact hx
    letI : Algebra (Γ(X, U) ⧸ I.ideal U)
        I.subscheme.functionField :=
      I.quotientStalkAlgebra U (genericPoint I.subscheme) hmem
    FractionRing (Γ(X, U) ⧸ I.ideal U) ≃ₐ[Γ(X, U) ⧸ I.ideal U]
      I.subscheme.functionField := by
  let I := pointClosureIdealSheaf x
  have hmem : genericPoint I.subscheme ∈
      I.subschemeι ⁻¹ᵁ (U : X.Opens) := by
    change I.subschemeι (genericPoint I.subscheme) ∈ (U : X.Opens)
    rw [pointClosureSubschemeι_genericPoint]
    exact hx
  letI : Algebra (Γ(X, U) ⧸ I.ideal U)
      I.subscheme.functionField :=
    I.quotientStalkAlgebra U (genericPoint I.subscheme) hmem
  letI : IsFractionRing (Γ(X, U) ⧸ I.ideal U)
      I.subscheme.functionField :=
    pointClosure_functionField_isFractionRing x U hx
  exact FractionRing.algEquiv (A := Γ(X, U) ⧸ I.ideal U)
    I.subscheme.functionField

/-- For an actual finite scheme map, the two quotient fields in the
all-centre specialization theorem are the generic stalk fields of the
source point closure and its image point closure, respectively. -/
theorem finitePreimage_pointClosure_genericFields
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme Y]
    (U : Y.affineOpens)
    [Algebra k Γ(Y, U)] [Algebra.FiniteType k Γ(Y, U)]
    [CharP Γ(Y, U) p]
    (hmono : IsPrimeToPMonodromyMap p f)
    (x : X) (hx : x ∈ (finitePreimageAffine f U : X.Opens)) :
    let A := pointClosureIdealSheaf x
    let D := pointClosureIdealSheaf (f x)
    let W := finitePreimageAffine f U
    letI : Algebra Γ(Y, U) Γ(X, W) := (f.app U).hom.toAlgebra
    let Q : Ideal Γ(X, W) := A.ideal W
    let P : Ideal Γ(Y, U) := D.ideal U
    let hX : genericPoint A.subscheme ∈ A.subschemeι ⁻¹ᵁ (W : X.Opens) := by
      change A.subschemeι (genericPoint A.subscheme) ∈ (W : X.Opens)
      rw [pointClosureSubschemeι_genericPoint]
      exact hx
    let hY : genericPoint D.subscheme ∈ D.subschemeι ⁻¹ᵁ (U : Y.Opens) := by
      change D.subschemeι (genericPoint D.subscheme) ∈ (U : Y.Opens)
      rw [pointClosureSubschemeι_genericPoint]
      exact hx
    letI : Algebra (Γ(X, W) ⧸ Q) A.subscheme.functionField :=
      A.quotientStalkAlgebra W (genericPoint A.subscheme) hX
    letI : Algebra (Γ(Y, U) ⧸ P) D.subscheme.functionField :=
      D.quotientStalkAlgebra U (genericPoint D.subscheme) hY
    letI : Q.IsPrime := pointClosureIdealSheaf_ideal_isPrime x W hx
    Q.under Γ(Y, U) = P ∧
      IsFractionRing (Γ(X, W) ⧸ Q) A.subscheme.functionField ∧
      IsFractionRing (Γ(Y, U) ⧸ P) D.subscheme.functionField ∧
      (letI : Algebra (FractionRing (Γ(Y, U) ⧸ Q.under Γ(Y, U)))
          (FractionRing (Γ(X, W) ⧸ Q)) := centreFieldAlgebra Q;
        IsPrimeToPMonodromy.{u, u, u} p
          (FractionRing (Γ(Y, U) ⧸ Q.under Γ(Y, U)))
          (FractionRing (Γ(X, W) ⧸ Q))) := by
  let W := finitePreimageAffine f U
  let A := pointClosureIdealSheaf x
  let D := pointClosureIdealSheaf (f x)
  letI : Algebra Γ(Y, U) Γ(X, W) := (f.app U).hom.toAlgebra
  let Q : Ideal Γ(X, W) := A.ideal W
  let P : Ideal Γ(Y, U) := D.ideal U
  have hX : genericPoint A.subscheme ∈ A.subschemeι ⁻¹ᵁ (W : X.Opens) := by
    change A.subschemeι (genericPoint A.subscheme) ∈ (W : X.Opens)
    rw [pointClosureSubschemeι_genericPoint]
    exact hx
  have hY : genericPoint D.subscheme ∈ D.subschemeι ⁻¹ᵁ (U : Y.Opens) := by
    change D.subschemeι (genericPoint D.subscheme) ∈ (U : Y.Opens)
    rw [pointClosureSubschemeι_genericPoint]
    exact hx
  letI : Algebra (Γ(X, W) ⧸ Q) A.subscheme.functionField :=
    A.quotientStalkAlgebra W (genericPoint A.subscheme) hX
  letI : Algebra (Γ(Y, U) ⧸ P) D.subscheme.functionField :=
    D.quotientStalkAlgebra U (genericPoint D.subscheme) hY
  letI : Q.IsPrime := pointClosureIdealSheaf_ideal_isPrime x W hx
  have hresult := finiteNormalAffinePreimage_pointClosure_primeToPMonodromy
    p hp k f U hmono x hx
  exact ⟨hresult.1,
    pointClosure_functionField_isFractionRing x W hx,
    pointClosure_functionField_isFractionRing (f x) U hx,
    hresult.2⟩

#print axioms pointClosure_functionField_isFractionRing
#print axioms pointClosure_fractionRingAlgEquiv
#print axioms finitePreimage_pointClosure_genericFields

end Pcf
