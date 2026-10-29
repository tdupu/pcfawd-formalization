/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossPhiMonodromy
public import Pcf.Examples.PaperP.MonodromyLossReturnScheme
public import Pcf.Bounding.SchemePrimeToPIteration

/-!
# `F(P, z) = (φ(P), 1/z)` on `E ×ₖ ℙ¹` and the iterate `φ²` (`ex:monodromy-loss`)

For `latex/paper-p.tex`, Example `ex:monodromy-loss`: "`F(P,z) = (φ(P), 1/z)` is an étale
degree-2 self-map of `E × ℙ¹`" and "The return is covered by the degree-4 map
`F²|_{E×{0}}`, whose monodromy is prime to 3".

* `invForms`, **`inv`**: `z ↦ 1/z` on `ℙ¹ = Proj k[u, v]`, the forms map `[v : u]`;
  `inv_isFinite`, **`inv_etale`** (Jacobian determinant `-1`), `inv_toSpec`.
* **`bigF`** `= φ ×ₖ inv : E ×ₖ ℙ¹ ⟶ E ×ₖ ℙ¹` (`pullback.map`), **`bigF_isFinite`**,
  **`bigF_etale`**.
* **`phiSq_genericDegree`** (`φ² = φ ≫ φ` has generic degree 4) and
  **`phiSq_isPrimeToPMonodromyMap`** (prime-to-`p` monodromy for `p ≠ 2`, in particular 3).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial
namespace Pcf.Examples.PaperP.MonodromyLossProduct
open Pcf.Examples.PaperP.MonodromyLossCurve
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra
universe u

section Inv
variable (k : Type u) [Field k]

local notation "Coords" => BasilicaProjectiveScheme.Coordinates k
local notation "uu" => (X (Sum.inl 0) : BasilicaProjectiveScheme.Coordinates k)
local notation "vv" => (X (Sum.inr ()) : BasilicaProjectiveScheme.Coordinates k)

/-- The forms `[v : u]` of `z ↦ 1/z`. -/
noncomputable def invForms : BasilicaProjectiveScheme.Index → Coords
  | Sum.inl _ => vv
  | Sum.inr _ => uu

theorem invForms_homogeneous (j : BasilicaProjectiveScheme.Index) :
    (invForms k j).IsHomogeneous 1 := by
  rcases j with _ | _ <;> exact isHomogeneous_X k _

theorem invForms_cover : Pcf.PaperPFormsCoverProjective (invForms k) := by
  apply (Pcf.paperPIrrelevant_le_coordinateIdeal (K := k) (n := 1)).trans
  change Ideal.span (Set.range (X : BasilicaProjectiveScheme.Index → Coords)) ≤
    (Ideal.span (Set.range (invForms k))).radical
  rw [Ideal.span_le, Set.range_subset_iff]
  intro j
  apply Ideal.le_radical
  rcases j with j | j
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    exact Ideal.subset_span ⟨Sum.inr (), rfl⟩
  · exact Ideal.subset_span ⟨Sum.inl 0, rfl⟩

/-- **`z ↦ 1/z` on `ℙ¹`.** -/
noncomputable def inv :
    Proj (BasilicaProjectiveScheme.grading k) ⟶ Proj (BasilicaProjectiveScheme.grading k) :=
  Pcf.paperPFormsProjectiveSchemeMap (invForms k) 1 (by decide) (invForms_homogeneous k)
    (invForms_cover k)

instance inv_isFinite : IsFinite (inv k) := by
  unfold inv; infer_instance

theorem inv_jacobian_det : Matrix.det (fun a b => pderiv b (invForms k a)) = -1 := by
  let e : BasilicaProjectiveScheme.Index ≃ Fin 2 :=
    (Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans finSumFinEquiv
  rw [← Matrix.det_reindex_self e, Matrix.det_fin_two]
  have h0 : e.symm 0 = Sum.inl 0 := rfl
  have h1 : e.symm 1 = Sum.inr () := rfl
  simp [Matrix.reindex_apply, h0, h1, invForms, pderiv_X]

theorem inv_etaleAt (x : Proj (BasilicaProjectiveScheme.grading k)) :
    Pcf.Stacks.IsStacksEtaleAt (inv k) x := by
  unfold inv
  rw [Pcf.paperPFormsProjective_etaleAt_iff (invForms k) 1 (by decide)
    (invForms_homogeneous k) (invForms_cover k) (by simp), inv_jacobian_det]
  exact Ideal.notMem_of_isUnit _ isUnit_one.neg

/-- **`z ↦ 1/z` is étale.** -/
instance inv_etale : Etale (inv k) := by
  have hPl : RingHom.HoldsForLocalizationAway @RingHom.Etale := by
    intro R S _ _ _ r _
    rw [RingHom.etale_algebraMap]
    exact Algebra.Etale.of_isLocalizationAway r
  rw [HasRingHomProperty.iff_exists_appLE (P := @Etale)
    (RingHom.Etale.stableUnderComposition.stableUnderCompositionWithLocalizationAway hPl).1]
  intro x
  obtain ⟨U, hU, V, hV, hUV, hx, h⟩ := inv_etaleAt k x
  exact ⟨⟨V, hV⟩, ⟨U, hU⟩, hx, hUV, h⟩

theorem inv_toSpec : inv k ≫ BasilicaProjectiveScheme.structureMap k =
    BasilicaProjectiveScheme.structureMap k := by
  unfold inv BasilicaProjectiveScheme.structureMap
  rw [Pcf.paperPFormsProjective_toSpecZero_assoc]

end Inv

section BigF
variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

/-- `E ×ₖ ℙ¹`. -/
noncomputable abbrev EP1 : Scheme.{u} :=
  pullback (toSpec k) (BasilicaProjectiveScheme.structureMap k)

/-- **`F(P, z) = (φ(P), 1/z)`** on `E ×ₖ ℙ¹`. -/
noncomputable def bigF : EP1 k ⟶ EP1 k :=
  pullback.map (toSpec k) (BasilicaProjectiveScheme.structureMap k) (toSpec k)
    (BasilicaProjectiveScheme.structureMap k) (phi k i hi) (inv k) (𝟙 _)
    (by rw [Category.comp_id, phi_toSpec]) (by rw [Category.comp_id, inv_toSpec])

theorem bigF_fst : bigF k i hi ≫ pullback.fst _ _ = pullback.fst _ _ ≫ phi k i hi :=
  pullback.lift_fst _ _ _

theorem bigF_snd : bigF k i hi ≫ pullback.snd _ _ = pullback.snd _ _ ≫ inv k :=
  pullback.lift_snd _ _ _

/-- **`F` is finite.** -/
instance bigF_isFinite : IsFinite (bigF k i hi) :=
  MorphismProperty.pullbackMap (P := @IsFinite) (phi_isFinite k i hi) (inv_isFinite k)
    (phi_toSpec k i hi).symm (inv_toSpec k).symm

/-- **`F` is étale.** -/
instance bigF_etale : Etale (bigF k i hi) :=
  MorphismProperty.pullbackMap (P := @Etale) (phi_etale k i hi) (inv_etale k)
    (phi_toSpec k i hi).symm (inv_toSpec k).symm

end BigF

section Iterate
variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

/-- `φ² = φ ≫ φ` (which is `2ι`). -/
noncomputable abbrev phiSq : E k ⟶ E k := phi k i hi ≫ phi k i hi

theorem phi_genericDegree_at (y : E k) (hy : y = genericPoint (E k)) :
    letI := ((phi k i hi).stalkMap y).hom.toAlgebra
    Module.finrank ((E k).presheaf.stalk (phi k i hi y)) ((E k).presheaf.stalk y) = 2 := by
  subst hy; exact phi_genericDegree k i hi

theorem phi_genericPoint : phi k i hi (genericPoint (E k)) = genericPoint (E k) :=
  Pcf.map_genericPoint_eq_of_isDominant (phi k i hi)

/-- **`φ²` has generic degree 4.** -/
theorem phiSq_genericDegree :
    letI := ((phiSq k i hi).stalkMap (genericPoint (E k))).hom.toAlgebra
    Module.finrank ((E k).presheaf.stalk (phiSq k i hi (genericPoint (E k))))
      ((E k).presheaf.stalk (genericPoint (E k))) = 4 := by
  let f := phi k i hi
  let x := genericPoint (E k)
  have hfx : f x = x := phi_genericPoint k i hi
  have hR : IsField ((E k).presheaf.stalk (f (f x))) := by
    rw [hfx, hfx]; exact Field.toIsField _
  have hS : IsField ((E k).presheaf.stalk (f x)) := by
    rw [hfx]; exact Field.toIsField _
  letI : Field ((E k).presheaf.stalk (f (f x))) := hR.toField
  letI : Field ((E k).presheaf.stalk (f x)) := hS.toField
  letI : Algebra ((E k).presheaf.stalk (f (f x))) ((E k).presheaf.stalk (f x)) :=
    (f.stalkMap (f x)).hom.toAlgebra
  letI : Algebra ((E k).presheaf.stalk (f x)) ((E k).presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  letI : Algebra ((E k).presheaf.stalk (f (f x))) ((E k).presheaf.stalk x) :=
    ((f ≫ f).stalkMap x).hom.toAlgebra
  letI : IsScalarTower ((E k).presheaf.stalk (f (f x))) ((E k).presheaf.stalk (f x))
      ((E k).presheaf.stalk x) := IsScalarTower.of_algebraMap_eq' (by
    change ((f ≫ f).stalkMap x).hom = (f.stalkMap x).hom.comp (f.stalkMap (f x)).hom
    rw [Scheme.Hom.stalkMap_comp]
    rfl)
  have h1 : Module.finrank ((E k).presheaf.stalk (f (f x))) ((E k).presheaf.stalk (f x)) = 2 :=
    phi_genericDegree_at k i hi (f x) hfx
  have h2 : Module.finrank ((E k).presheaf.stalk (f x)) ((E k).presheaf.stalk x) = 2 :=
    phi_genericDegree k i hi
  change Module.finrank ((E k).presheaf.stalk (f (f x))) ((E k).presheaf.stalk x) = 4
  rw [← Module.finrank_mul_finrank _ ((E k).presheaf.stalk (f x)), h1, h2]

/-- **`φ²` has prime-to-`p` monodromy** for every prime `p ≠ 2`, in particular `p = 3`. -/
theorem phiSq_isPrimeToPMonodromyMap (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    Pcf.IsPrimeToPMonodromyMap p (phiSq k i hi) :=
  Pcf.isPrimeToPMonodromyMap_comp p _ _ (phi_isPrimeToPMonodromyMap k i hi p hp2)
    (phi_isPrimeToPMonodromyMap k i hi p hp2)

theorem phiSq_isPrimeToThreeMonodromy : Pcf.IsPrimeToPMonodromyMap 3 (phiSq k i hi) :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  phiSq_isPrimeToPMonodromyMap k i hi 3 (by decide)

/-- `F² = φ² ×ₖ inv²` on `E ×ₖ ℙ¹`: its first component is `φ²`. -/
theorem bigF_sq_fst : (bigF k i hi ≫ bigF k i hi) ≫ pullback.fst _ _ =
    pullback.fst _ _ ≫ phiSq k i hi := by
  rw [Category.assoc, bigF_fst, ← Category.assoc, bigF_fst, Category.assoc]

end Iterate

#print axioms inv_etale
#print axioms bigF_isFinite
#print axioms bigF_etale
#print axioms phiSq_genericDegree
#print axioms phiSq_isPrimeToThreeMonodromy
#print axioms bigF_sq_fst

end Pcf.Examples.PaperP.MonodromyLossProduct
