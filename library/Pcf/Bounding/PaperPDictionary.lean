/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeDeltaEtaleNoetherian
public import Pcf.Bounding.CriticalLoci

/-!
# The codimension-one étaleness dictionary in `paper-p.tex`

An actual finite morphism over a locally Noetherian scheme is locally of
finite presentation. Thus étaleness at a divisor's generic point can be
expressed by étale affine charts around that point, without adding a
presentation hypothesis to the paper's statement.
-/

@[expose] public section

namespace Pcf
open AlgebraicGeometry
universe u

/-- `paper-p.tex`, Lemma `lem:dictionary`: weighted local degree one at an
integral effective divisor is equivalent to the existence of affine
neighborhoods on which the finite morphism is étale.

`paper-p.tex` correspondence: Remark 2.3 (`rem:why-normalized`), Lemma 2.4 (`lem:dictionary`). -/
theorem paperP_divisorDelta_eq_one_iff_etaleAt
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormalScheme Y]
    (d : SchemeDivisorPoint X) :
    schemeDivisorDelta f d = 1 ↔
      ∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V)
        (hVU : V ≤ f ⁻¹ᵁ U), d.1 ∈ V ∧ (f.appLE U V hVU).hom.Etale := by
  constructor
  · intro hδ
    exact exists_etale_of_formallyEtale_stalk f d.1
      ((schemeDivisorDelta_eq_one_iff_formallyEtale f d).mp hδ)
  · rintro ⟨U, hU, V, hV, hVU, hdV, hEtale⟩
    apply (schemeDivisorDelta_eq_one_iff_formallyEtale f d).mpr
    algebraize [(f.appLE U V hVU).hom]
    exact (formallyEtale_stalkMap_iff U hU V hV hVU hdV).mpr
      (inferInstanceAs (Algebra.IsEtaleAt _ _))

#print axioms paperP_divisorDelta_eq_one_iff_etaleAt

end Pcf
