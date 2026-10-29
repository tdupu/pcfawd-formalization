/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.RegularToSmoothPerfectField
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The singular locus over a perfect field is closed

For a scheme `X` locally of finite type over a perfect field `k`, a point has a
regular local ring if and only if `X → Spec k` is smooth at it. Hence the
pointwise singular locus `stalkSingularLocus X` is the complement of the open
smooth locus, and is closed.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

set_option backward.isDefEq.respectTransparency false in
/-- A point with regular local ring is a smooth point over a perfect field. -/
theorem mem_smoothLocus_of_isRegularLocalRing_stalk_of_perfectField
    (k : Type u) [Field k] [PerfectField k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : X) (hx : IsRegularLocalRing (X.presheaf.stalk x)) : x ∈ f.smoothLocus := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hVU : V ≤ f ⁻¹ᵁ ⊤ := by simp
  let := (f.appLE ⊤ V hVU).hom.toAlgebra
  have hft : Algebra.FiniteType Γ(Spec (.of k), ⊤) Γ(X, V) :=
    f.finiteType_appLE (isAffineOpen_top _) hV hVU
  set q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  rw [Scheme.Hom.mem_smoothLocus,
    formallySmooth_stalkMap_iff ⊤ (isAffineOpen_top _) V hV hVU hxV]
  change Algebra.FormallySmooth Γ(Spec (.of k), ⊤) (Localization.AtPrime q)
  -- transport regularity from the stalk to the localization
  let : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) q := hV.isLocalization_stalk ⟨x, hxV⟩
  have : IsRegularLocalRing (Localization.AtPrime q) :=
    IsRegularLocalRing.of_ringEquiv
      (IsLocalization.algEquiv q.primeCompl (X.presheaf.stalk x)
        (Localization.AtPrime q)).toRingEquiv
  -- make everything a `k`-algebra through `k ≅ Γ(Spec k, ⊤)`
  let eΓ : k ≃+* Γ(Spec (.of k), ⊤) :=
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv
  let : Algebra k Γ(Spec (.of k), ⊤) := eΓ.toRingHom.toAlgebra
  let : Algebra k Γ(X, V) :=
    ((algebraMap Γ(Spec (.of k), ⊤) Γ(X, V)).comp (algebraMap k Γ(Spec (.of k), ⊤))).toAlgebra
  have : IsScalarTower k Γ(Spec (.of k), ⊤) Γ(X, V) := .of_algebraMap_eq' rfl
  have hsurj : Function.Surjective (algebraMap k Γ(Spec (.of k), ⊤)) := eΓ.surjective
  have : Algebra.FiniteType k Γ(Spec (.of k), ⊤) :=
    Algebra.FiniteType.of_surjective (Algebra.ofId k _) hsurj
  have : Algebra.FiniteType k Γ(X, V) := .trans this hft
  have : Algebra.IsSmoothAt k q := isSmoothAt_of_isRegularLocalRing_of_perfectField k Γ(X, V) q
  have : IsScalarTower k Γ(Spec (.of k), ⊤) (Localization.AtPrime q) :=
    .of_algebraMap_eq' <| by
      rw [IsScalarTower.algebraMap_eq k Γ(X, V) (Localization.AtPrime q),
        IsScalarTower.algebraMap_eq Γ(Spec (.of k), ⊤) Γ(X, V) (Localization.AtPrime q)]
      rfl
  have : Algebra.FormallyUnramified k Γ(Spec (.of k), ⊤) :=
    .of_surjective (Algebra.ofId k _) hsurj
  exact Algebra.FormallySmooth.of_restrictScalars k _ _

/-- Over a perfect field, the singular locus of a scheme locally of finite type
is exactly the complement of the smooth locus. -/
theorem stalkSingularLocus_eq_compl_smoothLocus_of_perfectField
    (k : Type u) [Field k] [PerfectField k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    stalkSingularLocus X = (f.smoothLocus : Set X)ᶜ := by
  have : IsRegularRing (CommRingCat.of k) := inferInstanceAs (IsRegularRing k)
  refine (stalkSingularLocus_subset_compl_smoothLocus (.of k) f).antisymm fun x hx hreg ↦ ?_
  exact hx (mem_smoothLocus_of_isRegularLocalRing_stalk_of_perfectField k f x
    (by simpa [stalkSingularLocus] using hreg))

/-- Restricted form of Stacks Lemma 29.19.3 (1): the singular locus of a scheme
locally of finite type over a perfect field is closed.

Divergence from Stacks: Stacks proves the J-2 property (openness of the regular
locus on every scheme locally of finite type over the base) over an arbitrary
field. This declaration assumes `k` perfect and asserts only closedness of the
singular locus of `X` itself. -/
@[stacks 07R5 "(1), perfect base field, closedness of the singular locus of X only"]
theorem isClosed_stalkSingularLocus_of_perfectField
    (k : Type u) [Field k] [PerfectField k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    IsClosed (stalkSingularLocus X) := by
  rw [stalkSingularLocus_eq_compl_smoothLocus_of_perfectField k f]
  exact f.smoothLocus.isOpen.isClosed_compl

/-- The characteristic-zero case of `isClosed_stalkSingularLocus_of_perfectField`. -/
theorem isClosed_stalkSingularLocus_of_charZero
    (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    IsClosed (stalkSingularLocus X) :=
  isClosed_stalkSingularLocus_of_perfectField k f

#print axioms mem_smoothLocus_of_isRegularLocalRing_stalk_of_perfectField
#print axioms stalkSingularLocus_eq_compl_smoothLocus_of_perfectField
#print axioms isClosed_stalkSingularLocus_of_perfectField
#print axioms isClosed_stalkSingularLocus_of_charZero

end Pcf
