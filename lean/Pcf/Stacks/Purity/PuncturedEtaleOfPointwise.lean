/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Etale.Locus
public import Pcf.Stacks.Purity.PuncturedSpectrum

/-!
# Etaleness over the punctured spectrum from pointwise etaleness

Let `R` be a local ring and `S` a finitely presented `R`-algebra.  The target predicate of
Stacks Tag `0BM9` asks that `Spec S → Spec R` become etale after pullback to the punctured
spectrum `U = Spec R \ {m}`.  This file proves that this scheme statement follows from the
pointwise algebraic statement: `S` is etale over `R` at every prime of `S` not lying over `m`.

The proof covers the preimage of `U` by basic opens `D(b)`; each such `D(b)` lies in the etale
locus, so `S_b` is etale over `R`.  Etaleness is local on the source, and the open immersion
`U → Spec R` may be cancelled because it is unramified.  This is the converse of
`Pcf.Stacks.Algebra.isEtaleAt_of_puncturedSpectrum_pullback_etale`.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Pcf.Stacks

/-- Etaleness of scheme morphisms respects isomorphisms. -/
theorem etale_respectsIso : MorphismProperty.RespectsIso (@Etale.{u}) := by
  rw [HasRingHomProperty.eq_affineLocally (@Etale)]
  exact affineLocally_respectsIso _ RingHom.Etale.respectsIso

/-- If every point of an open `W ⊆ Spec S` is in the etale locus of `S` over `R`, then the
composite `W → Spec S → Spec R` is etale. -/
theorem etale_opens_ι_comp_of_forall_isEtaleAt
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S]
    (W : (Spec (.of S)).Opens)
    (hW : ∀ x : Spec (.of S), x ∈ W →
      (show PrimeSpectrum S from x) ∈ Algebra.etaleLocus R S) :
    Etale (W.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  have : IsZariskiLocalAtSource (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u})
  have : MorphismProperty.RespectsIso (@Etale.{u}) := etale_respectsIso
  let f : Spec (.of S) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let ι' := {b : S // (PrimeSpectrum.basicOpen b : (Spec (.of S)).Opens) ≤ W}
  let V : ι' → W.toScheme.Opens := fun b ↦ W.ι ⁻¹ᵁ (PrimeSpectrum.basicOpen b.1)
  have hV : iSup V = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    have hxW : W.ι x ∈ W := x.2
    obtain ⟨_, ⟨b, rfl⟩, hxb, hbW⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxW W.2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨b, hbW⟩, hxb⟩
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Etale) V hV fun ⟨b, hb⟩ ↦ ?_
  have hEt : Algebra.Etale R (Localization.Away b) := by
    rw [← Algebra.basicOpen_subset_etaleLocus_iff_etale]
    intro x hx
    exact hW x (hb hx)
  have hspec : Etale (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away b)))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hEt)
  have hcomp : (Scheme.Opens.isoOfLE hb).inv ≫ (V ⟨b, hb⟩).ι ≫ W.ι ≫ f =
      (basicOpenIsoSpecAway (R := .of S) b).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away b))) := by
    have h2 : ((Scheme.Opens.isoOfLE hb).inv ≫ (V ⟨b, hb⟩).ι ≫ W.ι) ≫ f =
        Scheme.Opens.ι (X := Spec (.of S)) (PrimeSpectrum.basicOpen b) ≫ f :=
      congrArg (· ≫ f) (Scheme.Opens.isoOfLE_inv_ι hb)
    simp only [Category.assoc] at h2
    rw [h2, ← basicOpenIsoSpecAway_hom_SpecMap (R := .of S) b, Category.assoc]
    congr 1
    dsimp only [f]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have h1 : Etale ((Scheme.Opens.isoOfLE hb).inv ≫ (V ⟨b, hb⟩).ι ≫ W.ι ≫ f) := by
    rw [hcomp]
    infer_instance
  rw [MorphismProperty.cancel_left_of_respectsIso (P := @Etale)] at h1
  rwa [← Category.assoc] at h1

/-- **Etaleness over the punctured spectrum from pointwise etaleness.**

If a finitely presented algebra over a local ring is etale at every prime not lying over the
maximal ideal, then its spectrum is etale after pullback to the punctured spectrum.  This is the
converse of `Pcf.Stacks.Algebra.isEtaleAt_of_puncturedSpectrum_pullback_etale`, and converts the
pointwise output of the induction in Tag `0BMB` into the target predicate of Tag `0BM9`. -/
theorem etale_puncturedSpectrum_pullback_of_forall_isEtaleAt
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
    [Algebra.FinitePresentation R S]
    (h : ∀ (q : Ideal S) [q.IsPrime], q.under R ≠ IsLocalRing.maximalIdeal R →
      Algebra.IsEtaleAt R q) :
    Etale (((Over.pullback (puncturedSpectrum R).ι).obj
      ((algSpec (.of R)).obj (Opposite.op (.of R S)))).hom) := by
  let f : Spec (.of S) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R S))
  let U : (Spec (.of R)).Opens := puncturedSpectrum R
  change Etale (pullback.snd f U.ι)
  have : MorphismProperty.RespectsIso (@Etale.{u}) := etale_respectsIso
  have hW : Etale ((f ⁻¹ᵁ U).ι ≫ f) := by
    refine etale_opens_ι_comp_of_forall_isEtaleAt (f ⁻¹ᵁ U) fun x hx ↦ ?_
    apply h
    intro hq
    have hx' := (mem_puncturedSpectrum_iff R (f x)).mp hx
    apply hx'
    ext1
    exact hq
  have hcomp : Etale (pullback.snd f U.ι ≫ U.ι) := by
    rw [← pullback.condition, ← pullbackRestrictIsoRestrict_hom_ι f U, Category.assoc,
      MorphismProperty.cancel_left_of_respectsIso (P := @Etale)]
    exact hW
  exact Etale.of_comp (pullback.snd f U.ι) U.ι

#print axioms etale_respectsIso
#print axioms etale_opens_ι_comp_of_forall_isEtaleAt
#print axioms etale_puncturedSpectrum_pullback_of_forall_isEtaleAt

end Pcf.Stacks
