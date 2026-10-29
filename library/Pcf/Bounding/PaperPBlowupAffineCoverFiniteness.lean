/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupTowerPCFBridge
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Gluing finite branch support over a finite affine cover

Once a global blow-up and its lifted branch sets are constructed, chartwise
finite branch support over affine opens gives finite global support. The
global construction and compatibility of the local lifts are separate.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

/-- Finiteness of a subset of a scheme is local on a finite open cover.
Each local preimage is mapped into the global set and the cover is jointly
surjective. -/
theorem finite_of_finite_on_finite_openCover
    {Y : Scheme.{u}} (𝒰 : Y.OpenCover) [Finite 𝒰.I₀]
    (s : Set Y) (hlocal : ∀ i : 𝒰.I₀, (𝒰.f i ⁻¹' s).Finite) :
    s.Finite := by
  have hfin : (⋃ i : 𝒰.I₀, 𝒰.f i '' (𝒰.f i ⁻¹' s)).Finite :=
    Set.finite_iUnion (fun i => (hlocal i).image (𝒰.f i))
  apply hfin.subset
  intro y hy
  obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq y
  exact Set.mem_iUnion.mpr ⟨i, ⟨x, hy, rfl⟩⟩

/-- For a quasi-compact scheme, it suffices to check finiteness on each
member of its canonical affine cover. Compactness selects a finite
subcover. -/
theorem finite_of_finite_on_affineCover
    (Y : Scheme.{u}) [CompactSpace Y]
    (s : Set Y)
    (hlocal : ∀ i : Y.affineCover.I₀,
      (Y.affineCover.f i ⁻¹' s).Finite) :
    s.Finite := by
  let 𝒰 := Y.affineCover.finiteSubcover
  apply finite_of_finite_on_finite_openCover 𝒰 s
  intro i
  exact hlocal (Y.affineCover.idx i.1)

/-- The same local-to-global result for the union of every branch support
in a tower. This is the support-finiteness portion of global gluing. -/
theorem finite_union_branch_family_of_affineCover
    (Y : Scheme.{u}) [CompactSpace Y]
    (branch : ℕ → Set Y)
    (hlocal : ∀ i : Y.affineCover.I₀,
      (Y.affineCover.f i ⁻¹' (⋃ n, branch n)).Finite) :
    (⋃ n, branch n).Finite :=
  finite_of_finite_on_affineCover Y _ hlocal

#print axioms finite_of_finite_on_finite_openCover
#print axioms finite_of_finite_on_affineCover
#print axioms finite_union_branch_family_of_affineCover

end
end Pcf.Bounding.AllCodimBlowup
