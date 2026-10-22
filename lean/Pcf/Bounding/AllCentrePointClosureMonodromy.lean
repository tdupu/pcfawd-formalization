/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PointClosureMapCompatibility
public import Pcf.Bounding.SchemeAllCentreFieldCharacteristic

/-!
# Prime-to-characteristic monodromy at every integral centre

For a normal finite-type target in characteristic `p`, the image of every
point has an affine neighborhood with the characteristic and finite-type
conditions needed by the all-centre fibre theorem. This yields monodromy
for the actual finite map between reduced integral point closures.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry TopologicalSpace

universe u

set_option linter.style.haveILetI false

/-- The function-field extension of the reduced closure of every point in
a finite prime-to-`p` cover of a normal finite-type characteristic-`p`
scheme has prime-to-`p` monodromy. The field map is the actual generic
stalk map of the finite restriction morphism. -/
theorem finiteType_pointClosureMap_primeToPMonodromy
    (p : ℕ) (hp : p.Prime)
    (k : Type u) [Field k] [CharP k p]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (hmono : IsPrimeToPMonodromyMap p f)
    (x : X) :
    let g := pointClosureSubschemeMap f x (f x) rfl
    letI : IsFinite g := pointClosureSubschemeMap_isFinite f x (f x) rfl
    letI : IsDominant g := pointClosureSubschemeMap_isDominant f x (f x) rfl
    IsPrimeToPMonodromyMap p g := by
  let g := pointClosureSubschemeMap f x (f x) rfl
  letI : IsFinite g := pointClosureSubschemeMap_isFinite f x (f x) rfl
  letI : IsDominant g := pointClosureSubschemeMap_isDominant f x (f x) rfl
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f x)) isOpen_univ
  let W : Y.affineOpens := ⟨U, hU⟩
  have hx : x ∈ (finitePreimageAffine f W : X.Opens) := hxU
  letI : Algebra k Γ(Y, W) := schemeAffineAlgebraOfField k s W
  letI : Algebra.FiniteType k Γ(Y, W) :=
    schemeAffineAlgebraOfField_finiteType k s W
  letI : CharP Γ(Y, W) p := by
    letI : Nonempty (W : Y.Opens) := ⟨⟨f x, hxU⟩⟩
    exact schemeAffineAlgebraOfField_charP p hp k s W
  exact pointClosureSubschemeMap_primeToPMonodromy
    p hp k f W hmono x hx

#print axioms finiteType_pointClosureMap_primeToPMonodromy

end Pcf
