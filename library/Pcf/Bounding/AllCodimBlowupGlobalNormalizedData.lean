/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupGlobalNormalizedBranch
public import Pcf.Bounding.PaperPProjectiveDominant

/-!
# Normalized blow-up data along a proper integral closed subvariety

`latex/paper-p.tex`, Definition `def:normalized-blowup-data`, starts from a
finite surjective morphism `f : X ⟶ Y` of normal varieties and an integral
closed subvariety `A ⊊ X`, with generic point `a`. Its image `B = f(A)` is the
closure of `f a`; the centre on `Y` is the reduced ideal sheaf of `B`, and the
centre on `X` is its scheme-theoretic inverse image `f⁻¹(B)`, Mathlib's
`IdealSheafData.comap`. The normalized blow-ups are
`Y' = globalNormalizedBlowup (blowupCentre f a)` and
`X' = globalNormalizedBlowup ((blowupCentre f a).comap f)`.

Since `A ≠ X` and `f` is finite, `B ≠ Y`, so the generic point of `Y` is not
in the centre and all the constructions of the previous files apply.
-/

@[expose] public section
namespace Pcf.Bounding.AllCodimBlowup
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u
noncomputable section

variable {X Y : Scheme.{u}}

/-- The reduced centre `B = f(A)` on `Y`, for `A` the closure of `a`.

`paper-p.tex` correspondence: Definition 7.6 (`def:normalized-blowup-data`). -/
def blowupCentre (f : X ⟶ Y) (a : X) : Y.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨closure {f a}, isClosed_closure⟩

theorem blowupCentre_support (f : X ⟶ Y) (a : X) :
    ((blowupCentre f a).support : Set Y) = closure {f a} :=
  Scheme.IdealSheafData.coe_support_vanishingIdeal _

/-- The support of the centre is the image `f(A)` of `A = closure {a}`.

`paper-p.tex` correspondence: Definition 7.6 (`def:normalized-blowup-data`). -/
theorem blowupCentre_support_eq_image (f : X ⟶ Y) [IsFinite f] (a : X) :
    ((blowupCentre f a).support : Set Y) = f '' closure {a} := by
  rw [blowupCentre_support, ← Set.image_singleton,
    f.isClosedMap.closure_image_eq_of_continuous f.continuous]

/-- The image of a proper integral closed subvariety under a finite morphism of
integral schemes is proper: the centre misses the generic point.

`paper-p.tex` correspondence: Definition 7.6 (`def:normalized-blowup-data`). -/
theorem genericPoint_not_mem_blowupCentre [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f] (a : X) (ha : a ≠ genericPoint X) :
    genericPoint Y ∉ (blowupCentre f a).support := by
  intro hmem
  have hmem' : genericPoint Y ∈ closure ({f a} : Set Y) := by
    rw [← blowupCentre_support]
    exact hmem
  have hspec : f a ⤳ genericPoint Y := specializes_iff_mem_closure.mpr hmem'
  have hfa : f a = genericPoint Y :=
    (hspec.antisymm (genericPoint_specializes (f a))).eq
  have hle : a ≤ genericPoint X := genericPoint_specializes a
  have hlt : a < genericPoint X := lt_of_le_not_ge hle (fun hge ↦
    ha (Specializes.antisymm (show a ⤳ genericPoint X from hge)
      (genericPoint_specializes a)).eq)
  have hmono := schemeHom_strictMono_of_locallyQuasiFinite f hlt
  rw [map_genericPoint_eq_of_isDominant f, hfa] at hmono
  exact lt_irrefl _ hmono

/-- `latex/paper-p.tex`, Proposition `prop:normalized-blowup-construction`, in
the data of Definition `def:normalized-blowup-data`: for a finite dominant
morphism `f : X ⟶ Y` of integral schemes of finite type over `k` and the
generic point `a` of a proper integral closed subvariety `A ⊊ X`, there is a
unique finite surjective morphism `f' : X' ⟶ Y'` of the normalized blow-ups
with `β ∘ f' = f ∘ α`.

`paper-p.tex` correspondence: Proposition 7.7 (`prop:normalized-blowup-construction`). -/
theorem normalizedBlowupData_existsUnique [IsIntegral X] [IsIntegral Y]
    (k : Type u) [Field k] (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f] (a : X) (ha : a ≠ genericPoint X) :
    haveI : Fact (genericPoint Y ∉ (blowupCentre f a).support) :=
      ⟨genericPoint_not_mem_blowupCentre f a ha⟩
    ∃! F : globalNormalizedBlowup ((blowupCentre f a).comap f) ⟶
        globalNormalizedBlowup (blowupCentre f a),
      IsFinite F ∧ Function.Surjective F ∧
        F ≫ globalNormalizedBlowupToBase (blowupCentre f a) =
          globalNormalizedBlowupToBase ((blowupCentre f a).comap f) ≫ f := by
  haveI : Fact (genericPoint Y ∉ (blowupCentre f a).support) :=
    ⟨genericPoint_not_mem_blowupCentre f a ha⟩
  exact globalNormalizedBlowupMap_existsUnique_finiteSurjective f _ k s

#print axioms genericPoint_not_mem_blowupCentre
#print axioms normalizedBlowupData_existsUnique

end
end Pcf.Bounding.AllCodimBlowup
