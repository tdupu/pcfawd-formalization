/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.PinchedLine
public import Pcf.Bounding.SchemeExtraction
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# `B` as the reduced closed subscheme `ν(V(w - 1))`, and `g = f|_B` canonically

For `paper-p.tex`, Example `ex:pinched` ("Let `B = ν(V(w - 1))` and `g = f|_B`"),
with the canonical restriction `pointClosureSubschemeMap` used throughout the
bounding development:

* `kerQuotientLine_eq`: the kernel of `Spec(R ⧸ 𝔭_B) → X` is the reduced
  point-closure ideal sheaf of the generic point `η_B = ν(η_{V(w-1)})`.
* `bSubschemeIso : (pointClosureIdealSheaf η_B).subscheme ≅ Spec R_B`, over `X`
  (`bSubschemeIso_inv_ι`), and
* `bSubschemeIso_gScheme`: under it the canonical restriction
  `pointClosureSubschemeMap f η_B η_B _` is the map `gScheme : p ↦ p(z²)` of
  `PinchedNodeFibre`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.PinchedLineScheme

open AlgebraicGeometry CategoryTheory Pcf.Examples.PaperP.PinchedNormalization
  Pcf.Examples.PaperP.PinchedLine

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u

variable (k : Type u) [Field k] [CharZero k]

local notation "R" => PinchedRing k
local notation "RB" => PinchedNodeFibre.NodeRing k

/-- The closed immersion `Spec(R ⧸ 𝔭_B) → X`. -/
noncomputable def lineQuotMap : Spec (.of (R ⧸ (bPoint k).asIdeal)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))

instance : IsClosedImmersion (lineQuotMap k) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The prime of `Γ(X, ⊤)` corresponding to a point of `X = Spec R`. -/
theorem primeIdealOf_top (x : Spec (.of R)) :
    ((isAffineOpen_top (Spec (.of R))).primeIdealOf ⟨x, trivial⟩).asIdeal =
      x.asIdeal.comap (Scheme.ΓSpecIso (.of R)).hom.hom := by
  have h := (isAffineOpen_top (Spec (.of R))).fromSpec_primeIdealOf ⟨x, trivial⟩
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  set p := (isAffineOpen_top (Spec (.of R))).primeIdealOf ⟨x, trivial⟩
  have hx : x.asIdeal = p.asIdeal.comap (Scheme.ΓSpecIso (.of R)).inv.hom :=
    congrArg (fun y : Spec (.of R) => y.asIdeal) h.symm
  rw [hx, Ideal.comap_comap, ← CommRingCat.hom_comp, Iso.hom_inv_id]
  rfl

theorem kerQuotientLine_eq : (lineQuotMap k).ker = Pcf.pointClosureIdealSheaf (bPoint k) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  have hK := congrArg (fun J => Scheme.IdealSheafData.equivOfIsAffine J)
    (Scheme.ker_of_isAffine (lineQuotMap k))
  simp only [Scheme.IdealSheafData.equivOfIsAffine_apply,
    ← Scheme.IdealSheafData.equivOfIsAffine_symm_apply] at hK
  have hK2 := (Scheme.IdealSheafData.equivOfIsAffine (X := Spec (.of R))).apply_symm_apply
    (RingHom.ker (lineQuotMap k).appTop.hom)
  rw [Scheme.IdealSheafData.equivOfIsAffine_apply] at hK2
  rw [hK, hK2, Pcf.pointClosureIdealSheaf_ideal (bPoint k) ⟨⊤, isAffineOpen_top _⟩ trivial]
  change _ = ((isAffineOpen_top (Spec (.of R))).primeIdealOf ⟨bPoint k, trivial⟩).asIdeal
  rw [primeIdealOf_top]
  have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (bPoint k).asIdeal))
  ext a
  rw [RingHom.mem_ker, Ideal.mem_comap]
  have e : (lineQuotMap k).appTop = (Scheme.ΓSpecIso (.of R)).hom ≫
      CommRingCat.ofHom (Ideal.Quotient.mk (bPoint k).asIdeal) ≫
        (Scheme.ΓSpecIso (.of (R ⧸ (bPoint k).asIdeal))).inv := by
    rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  rw [e]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  rw [map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).1,
    Ideal.Quotient.eq_zero_iff_mem]

#print axioms kerQuotientLine_eq

/-- The reduced closed subscheme `B = ν(V(w - 1)) ⊆ X`. -/
noncomputable abbrev bIdeal : (Spec (.of R)).IdealSheafData := Pcf.pointClosureIdealSheaf (bPoint k)

/-- Equal ideal sheaves have isomorphic subschemes. -/
noncomputable def kerIso : (lineQuotMap k).ker.subscheme ≅ (bIdeal k).subscheme where
  hom := Scheme.IdealSheafData.inclusion (kerQuotientLine_eq k).ge
  inv := Scheme.IdealSheafData.inclusion (kerQuotientLine_eq k).le
  hom_inv_id := by
    rw [Scheme.IdealSheafData.inclusion_comp, Scheme.IdealSheafData.inclusion_id]
  inv_hom_id := by
    rw [Scheme.IdealSheafData.inclusion_comp, Scheme.IdealSheafData.inclusion_id]

/-- `Spec(R ⧸ 𝔭_B) ≅ B`, over `X`. -/
noncomputable def quotIso : Spec (.of (R ⧸ (bPoint k).asIdeal)) ≅ (bIdeal k).subscheme :=
  asIso (lineQuotMap k).toImage ≪≫ kerIso k

theorem quotIso_hom_ι : (quotIso k).hom ≫ (bIdeal k).subschemeι = lineQuotMap k := by
  simp only [quotIso, kerIso, Iso.trans_hom, asIso_hom, Category.assoc,
    Scheme.IdealSheafData.inclusion_subschemeι]
  exact Scheme.Hom.toImage_imageι _

/-- `Spec R_B ≅ Spec(R ⧸ 𝔭_B)` from `R ⧸ 𝔭_B ≃+* R_B`. -/
noncomputable def lineSpecIso : Spec (.of RB) ≅ Spec (.of (R ⧸ (bPoint k).asIdeal)) :=
  Scheme.Spec.mapIso (quotientLineEquiv k).toCommRingCatIso.op

/-- **`B ≅ Spec R_B`**. -/
noncomputable def bSubschemeIso : (bIdeal k).subscheme ≅ Spec (.of RB) :=
  (quotIso k).symm ≪≫ (lineSpecIso k).symm

/-- The composite `Spec R_B ≅ B ↪ X` is `Spec` of the restriction `ρ : R → R_B`. -/
theorem bSubschemeIso_inv_ι :
    (bSubschemeIso k).inv ≫ (bIdeal k).subschemeι =
      Spec.map (CommRingCat.ofHom (lineRestr k)) := by
  simp only [bSubschemeIso, Iso.trans_inv, Iso.symm_inv, Category.assoc, quotIso_hom_ι]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1

/-- The canonical restriction `g = f|_B`. -/
noncomputable def gSub : (bIdeal k).subscheme ⟶ (bIdeal k).subscheme :=
  Pcf.pointClosureSubschemeMap (PinchedAmbient.fScheme k) (bPoint k) (bPoint k) (fScheme_bPoint k)

theorem lineQuotMap_comp_fScheme :
    lineQuotMap k ≫ PinchedAmbient.fScheme k =
      Spec.map (CommRingCat.ofHom (fStarLine k)) ≫ lineQuotMap k := by
  unfold lineQuotMap PinchedAmbient.fScheme
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

theorem quotIso_gSub :
    (quotIso k).hom ≫ gSub k = Spec.map (CommRingCat.ofHom (fStarLine k)) ≫ (quotIso k).hom := by
  apply (cancel_mono (bIdeal k).subschemeι).mp
  rw [Category.assoc, gSub, Pcf.pointClosureSubschemeMap_subschemeι, ← Category.assoc,
    quotIso_hom_ι, Category.assoc, quotIso_hom_ι, lineQuotMap_comp_fScheme]

theorem lineSpecIso_fStarLine :
    (lineSpecIso k).hom ≫ Spec.map (CommRingCat.ofHom (fStarLine k)) =
      PinchedNodeFibre.gScheme k ≫ (lineSpecIso k).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  exact (quotientLineEquiv_fStar k (Ideal.Quotient.mk (bPoint k).asIdeal x) :)

/-- **`g = f|_B` is `gScheme`**: under `B ≅ Spec R_B`, the canonical restriction of `f`
to the reduced closed subscheme `B` is `Spec(p ↦ p(z²))`.

`paper-p.tex` correspondence: Example A.9 (`ex:pinched`). -/
theorem bSubschemeIso_gScheme :
    gSub k = (bSubschemeIso k).hom ≫ PinchedNodeFibre.gScheme k ≫ (bSubschemeIso k).inv := by
  have hA : gSub k = (quotIso k).inv ≫ Spec.map (CommRingCat.ofHom (fStarLine k)) ≫
      (quotIso k).hom := by
    rw [← quotIso_gSub, Iso.inv_hom_id_assoc]
  have hB : Spec.map (CommRingCat.ofHom (fStarLine k)) =
      (lineSpecIso k).inv ≫ PinchedNodeFibre.gScheme k ≫ (lineSpecIso k).hom := by
    rw [← lineSpecIso_fStarLine, Iso.inv_hom_id_assoc]
  rw [hA, hB]
  simp only [bSubschemeIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Category.assoc]

#print axioms bSubschemeIso
#print axioms bSubschemeIso_inv_ι
#print axioms bSubschemeIso_gScheme

end Pcf.Examples.PaperP.PinchedLineScheme
