/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PointClosureMonodromy

/-!
# Monodromy across a generic-stalk comparison square

Prime-to-`p` monodromy of a finite dominant scheme map depends only on
its actual map of generic stalk fields. A commuting square of field
equivalences transports the normal-closure certificate.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry TopologicalSpace

universe u

set_option linter.style.haveILetI false

/-- A commuting pair of equivalences between actual generic-stalk
extensions transports prime-to-`p` monodromy of finite dominant scheme
morphisms. -/
theorem isPrimeToPMonodromyMap_of_genericStalkEquivs
    (p : ℕ)
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y]
    [IsFinite g] [IsDominant g] [IsIntegral X'] [IsIntegral Y']
    (eK : Y.presheaf.stalk (f (genericPoint X)) ≃+*
      Y'.presheaf.stalk (g (genericPoint X')))
    (eE : X.presheaf.stalk (genericPoint X) ≃+*
      X'.presheaf.stalk (genericPoint X'))
    (hcomm : (g.stalkMap (genericPoint X')).hom.comp eK.toRingHom =
      eE.toRingHom.comp (f.stalkMap (genericPoint X)).hom)
    (hmono : IsPrimeToPMonodromyMap p f) :
    IsPrimeToPMonodromyMap p g := by
  have hgp : f (genericPoint X) = genericPoint Y :=
    map_genericPoint_eq_of_isDominant f
  have hgp' : g (genericPoint X') = genericPoint Y' :=
    map_genericPoint_eq_of_isDominant g
  let e := (Y.presheaf.stalkCongr (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  let e' := (Y'.presheaf.stalkCongr (Inseparable.of_eq hgp')).commRingCatIsoToRingEquiv
  letI : Field (Y.presheaf.stalk (f (genericPoint X))) :=
    (e.toMulEquiv.isField (Field.toIsField _)).toField
  letI : Field (Y'.presheaf.stalk (g (genericPoint X'))) :=
    (e'.toMulEquiv.isField (Field.toIsField _)).toField
  letI : Algebra (Y.presheaf.stalk (f (genericPoint X)))
      (X.presheaf.stalk (genericPoint X)) :=
    (f.stalkMap (genericPoint X)).hom.toAlgebra
  letI : Algebra (Y'.presheaf.stalk (g (genericPoint X')))
      (X'.presheaf.stalk (genericPoint X')) :=
    (g.stalkMap (genericPoint X')).hom.toAlgebra
  change IsPrimeToPMonodromy.{u, u, u} p
    (Y.presheaf.stalk (f (genericPoint X)))
    (X.presheaf.stalk (genericPoint X)) at hmono
  change IsPrimeToPMonodromy.{u, u, u} p
    (Y'.presheaf.stalk (g (genericPoint X')))
    (X'.presheaf.stalk (genericPoint X'))
  exact isPrimeToPMonodromy_of_equiv_equiv p
    (Y.presheaf.stalk (f (genericPoint X)))
    (X.presheaf.stalk (genericPoint X))
    (Y'.presheaf.stalk (g (genericPoint X')))
    (X'.presheaf.stalk (genericPoint X'))
    eK eE hcomm hmono

#print axioms isPrimeToPMonodromyMap_of_genericStalkEquivs

end Pcf
