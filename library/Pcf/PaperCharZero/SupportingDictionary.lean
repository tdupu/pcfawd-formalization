/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeDeltaEtaleNoetherian
public import Pcf.Bounding.InvariantDivisorGeometry
public import Pcf.Stacks.Purity.Tag0BMBSchemeAPI

/-!
# Ramification index one and étaleness at an integral effective divisor

`paper.tex`, Lemma `lem:dictionary`, with an actual étale open neighborhood as
the final conclusion. The residue extension's separability is proved from the
structure morphism to the characteristic-zero field, and the existing local
criterion proves flatness from dominance and the normal target's DVR.
No flatness, residue separability, or finite presentation of the stalk algebra
is assumed. The source need only be integral, so the result includes the
manuscript's case where both varieties are normal.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace Pcf.PaperCharZero

variable {X Y : Scheme.{u}}

/-- Finite scheme morphisms over a characteristic-zero target field have
separable actual residue-field extensions. -/
theorem residueFieldMap_isSeparable_charZero
    (k : Type u) [Field k] [CharZero k] (s : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) [IsFinite f] (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x) := by
  let := (f.residueFieldMap x).hom.toAlgebra
  let : FiniteDimensional (Y.residueField (f x)) (X.residueField x) :=
    finiteResidueField_of_isFinite f x
  let := schemeStalkAlgebraOfField k s (f x)
  have : CharZero (Y.residueField (f x)) := charZero_of_injective_ringHom
    ((Y.residue (f x)).hom.comp (algebraMap k (Y.presheaf.stalk (f x)))).injective
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- For locally finitely presented scheme maps, formal étaleness of the actual
stalk map is equivalent to genuine étaleness on an open neighborhood. -/
theorem formallyEtale_stalkMap_iff_etale_neighborhood
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] (x : X) :
    (f.stalkMap x).hom.FormallyEtale ↔
      ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f) := by
  rw [← Pcf.Stacks.isStacksEtaleAt_iff_exists_etale]
  constructor
  · intro h
    obtain ⟨V, hV, U, hU, hUV, hx, he⟩ := exists_etale_of_formallyEtale_stalk f x h
    exact ⟨U, hU, V, hV, hUV, hx, he⟩
  · rintro ⟨U, hU, V, hV, hUV, hx, he⟩
    algebraize [(f.appLE V U hUV).hom]
    exact (formallyEtale_stalkMap_iff V hV U hU hUV hx).mpr
      (inferInstanceAs (Algebra.IsEtaleAt _ _))

/-- The actual divisorial ramification index is one iff the actual stalk map
is formally étale. This is the local algebra form of `lem:dictionary`.
Target normality supplies a DVR; characteristic zero supplies separability. -/
theorem ramificationIdx_eq_one_iff_formallyEtale_charZero
    (k : Type u) [Field k] [CharZero k] (s : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormalScheme Y]
    (P : SchemeDivisorPoint X) :
    schemeDivisorRamificationIdx f P = 1 ↔ (f.stalkMap P.1).hom.FormallyEtale := by
  rw [← schemeDivisorDelta_eq_one_iff_formallyEtale, schemeDivisorDelta_eq_one_iff]
  exact ⟨fun h => ⟨h, residueFieldMap_isSeparable_charZero k s f P.1⟩, And.left⟩

/-- `lem:dictionary`: ramification index one is equivalent to the existence
of an open neighborhood of the divisor generic point on which the actual
morphism is étale. Finite presentation of the morphism follows from the
finite map and locally Noetherian target; it is not an extra hypothesis.

Manuscript: `lem:dictionary` (Lemma 2.4). -/
theorem ramificationIdx_eq_one_iff_etale_at_divisor_charZero
    (k : Type u) [Field k] [CharZero k] (s : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormalScheme Y]
    (P : SchemeDivisorPoint X) :
    schemeDivisorRamificationIdx f P = 1 ↔
      ∃ U : X.Opens, P.1 ∈ U ∧ Etale (U.ι ≫ f) := by
  rw [ramificationIdx_eq_one_iff_formallyEtale_charZero k s f P]
  exact formallyEtale_stalkMap_iff_etale_neighborhood f P.1

end Pcf.PaperCharZero
