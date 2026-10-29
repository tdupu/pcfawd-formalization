/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossUnramified
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# `φ = 1 + ι` is unramified, quasi-finite and finite (`ex:monodromy-loss`)

For `latex/paper-p.tex`, Example `ex:monodromy-loss`: "The isogeny `φ` has degree 2, so
`F(P, z) = (φ(P), 1/z)` is an étale degree-2 self-map".

* `phi_prop_of_pieces`: a property local at the source, stable under composition and true for
  open immersions holds for `φ` once it holds for the three chart pieces `phi1, phi2, phi3`.
* **`phi_formallyUnramified`**, `phi_locallyOfFiniteType`, `phi_locallyQuasiFinite`.
* **`phi_isFinite`**: `φ` is finite. It is proper (`phi_isProper`) and locally quasi-finite;
  Mathlib's Zariski main theorem consequence `IsFinite.of_isProper_of_locallyQuasiFinite`
  then applies.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Polynomial
namespace Pcf.Examples.PaperP.MonodromyLossCurve
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
universe u

section
variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

instance AyToBw_isIso : IsIso (CommRingCat.ofHom (AyToBw k)) :=
  ⟨⟨CommRingCat.ofHom (BwToAy k), by
    ext a; exact congrArg (· a) (BwToAy_comp_AyToBw k), by
    ext a; exact congrArg (· a) (AyToBw_comp_BwToAy k)⟩⟩

theorem pieceA_phi1 : Spec.map (CommRingCat.ofHom (algebraMap (A k) (Ax k))) ≫ ιA k ≫ phi k i hi =
    Spec.map (CommRingCat.ofHom (phi1 k i hi)) ≫ ιA k := phi_D_x k i hi

theorem pieceA_phi2 : Spec.map (CommRingCat.ofHom (algebraMap (A k) (Aq k))) ≫ ιA k ≫ phi k i hi =
    Spec.map (CommRingCat.ofHom (phi2 k i hi)) ≫ ιB k := by
  rw [ιA_phi, phiA_D_q]

theorem pieceB_phi3 : Spec.map (CommRingCat.ofHom (algebraMap (B k) (Be k))) ≫ ιB k ≫ phi k i hi =
    Spec.map (CommRingCat.ofHom (phi3 k i hi)) ≫ ιB k := by
  rw [ιB_phi, phiB_D_e]

/-- **Locality on the three chart pieces.** -/
theorem phi_prop_of_pieces (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
    [P.IsStableUnderComposition]
    (hO : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f], P f)
    (h1 : P (Spec.map (CommRingCat.ofHom (phi1 k i hi))))
    (h2 : P (Spec.map (CommRingCat.ofHom (phi2 k i hi))))
    (h3 : P (Spec.map (CommRingCat.ofHom (phi3 k i hi)))) : P (phi k i hi) := by
  have hA : P (phiA k i hi) := by
    rw [IsZariskiLocalAtSource.iff_of_openCover (P := P)
      (Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of (A k)) (sA k) (sA_span k)).openCover]
    intro j
    have := SpecMap_glueGeneric (sA k) (sA_span k) (sA_ne_zero k) (toSpec k)
      (Spec.map (CommRingCat.ofHom (algebraMap k (A k)))) (gKA k i hi) (PA k i hi)
      (PA_hZ k i hi) (PA_hK k i hi) j
    change P (Spec.map _ ≫ phiA k i hi)
    unfold phiA
    rw [this]
    rcases j with ⟨_ | _⟩
    · exact P.comp_mem _ _ h1 (hO _)
    · exact P.comp_mem _ _ h2 (hO _)
  have hB : P (phiB k i hi) := by
    rw [IsZariskiLocalAtSource.iff_of_openCover (P := P)
      (Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of (B k)) (sBB k) (sBB_span k)).openCover]
    intro j
    have := SpecMap_glueGeneric (sBB k) (sBB_span k) (sBB_ne_zero k) (toSpec k)
      (Spec.map (CommRingCat.ofHom (algebraMap k (B k)))) (gKB k i hi) (QB k i hi)
      (QB_hZ k i hi) (QB_hK k i hi) j
    change P (Spec.map _ ≫ phiB k i hi)
    unfold phiB
    rw [this]
    rcases j with ⟨_ | _⟩
    · change P (Spec.map (CommRingCat.ofHom (AyToBw k)) ≫ jA k ≫ phiA k i hi)
      rw [← Category.assoc]
      refine P.comp_mem _ _ ?_ hA
      have : IsOpenImmersion (jA k) := by unfold jA; infer_instance
      exact hO _
    · exact P.comp_mem _ _ h3 (hO _)
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) (glueData k).openCover]
  rintro ⟨_ | _⟩
  · change P (ιA k ≫ phi k i hi); rw [ιA_phi]; exact hA
  · change P (ιB k ≫ phi k i hi); rw [ιB_phi]; exact hB

/-- **`φ` is formally unramified.** -/
instance phi_formallyUnramified : FormallyUnramified (phi k i hi) := by
  refine phi_prop_of_pieces k i hi @FormallyUnramified (fun f _ => inferInstance) ?_ ?_ ?_
  · rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
    exact phi1_formallyUnramified k i hi
  · rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
    exact phi2_formallyUnramified k i hi
  · rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
    exact phi3_formallyUnramified k i hi

instance phi_locallyOfFiniteType : LocallyOfFiniteType (phi k i hi) := by
  have : LocallyOfFiniteType (phi k i hi ≫ toSpec k) := by rw [phi_toSpec]; infer_instance
  exact locallyOfFiniteType_of_comp _ (toSpec k)

/-- A chart piece `Spec R ⟶ Spec S` composed with an open immersion equal to (open
immersion) `≫ φ` is locally of finite type. -/
theorem piece_finiteType {R S : CommRingCat.{u}} (f : R ⟶ S) (ι : Spec R ⟶ E k)
    {U : Scheme.{u}} (o : Spec S ⟶ U) (ι' : U ⟶ E k) [IsOpenImmersion o]
    [IsOpenImmersion ι'] (e : Spec.map f ≫ ι = o ≫ ι' ≫ phi k i hi) : f.hom.FiniteType := by
  have : LocallyOfFiniteType (Spec.map f ≫ ι) := by rw [e]; infer_instance
  have := locallyOfFiniteType_of_comp (Spec.map f) ι
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this

theorem quasiFinite_of_finiteType_of_formallyUnramified {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (h1 : f.FiniteType) (h2 : f.FormallyUnramified) : f.QuasiFinite := by
  letI := f.toAlgebra
  haveI : Algebra.FiniteType R S := h1
  haveI : Algebra.FormallyUnramified R S := h2
  exact (inferInstance : Algebra.QuasiFinite R S)

/-- **`φ` is locally quasi-finite.** -/
instance phi_locallyQuasiFinite : LocallyQuasiFinite (phi k i hi) := by
  refine phi_prop_of_pieces k i hi @LocallyQuasiFinite (fun f _ => inferInstance) ?_ ?_ ?_
  · rw [HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)]
    exact quasiFinite_of_finiteType_of_formallyUnramified _
      (piece_finiteType k i hi _ (ιA k) _ (ιA k) (pieceA_phi1 k i hi).symm)
      (phi1_formallyUnramified k i hi)
  · rw [HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)]
    exact quasiFinite_of_finiteType_of_formallyUnramified _
      (piece_finiteType k i hi _ (ιB k) _ (ιA k) (pieceA_phi2 k i hi).symm)
      (phi2_formallyUnramified k i hi)
  · rw [HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)]
    exact quasiFinite_of_finiteType_of_formallyUnramified _
      (piece_finiteType k i hi _ (ιB k) _ (ιB k) (pieceB_phi3 k i hi).symm)
      (phi3_formallyUnramified k i hi)

/-- **`φ : E ⟶ E` is finite.**

`paper-p.tex` correspondence: Example 4.6 (`ex:monodromy-loss`). -/
instance phi_isFinite : IsFinite (phi k i hi) :=
  IsFinite.of_isProper_of_locallyQuasiFinite _

end

#print axioms phi_formallyUnramified
#print axioms phi_locallyQuasiFinite
#print axioms phi_isFinite

end Pcf.Examples.PaperP.MonodromyLossCurve
