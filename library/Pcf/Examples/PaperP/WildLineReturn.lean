/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.WildGlobalPCF
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# The invariant line `H₀` of the wild example as an actual projective line

The graded specialization `x ↦ 0, y ↦ u, z ↦ v` induces, by functoriality of
`Proj`, an actual closed immersion `ι : ℙ¹ ⟶ ℙ²` with image `H₀`. The actual
global map restricts along `ι` to the projective-line morphism defined by the
forms `[u^(p+1) + c v^(p+1) : v^(p+1)]`, the homogenization of the displayed
return `t ↦ t^(p+1) + c` in the coordinate `t = u/v = y/z`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
namespace Pcf.Examples.PaperP.Wild
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra
variable (k : Type*) [Field k] (p : ℕ) (c : k)

abbrev LineIndex := Fin 1 ⊕ Unit
abbrev LineCoords := MvPolynomial LineIndex k
abbrev lineGrading := MvPolynomial.homogeneousSubmodule LineIndex k

noncomputable def lu : LineCoords k := X (Sum.inl 0)
noncomputable def lv : LineCoords k := X (Sum.inr ())

noncomputable def lineValues : Index → LineCoords k
  | Sum.inl j => if j = 0 then 0 else lu k
  | Sum.inr _ => lv k

noncomputable def lineSpecialization : Coordinates k →ₐ[k] LineCoords k := aeval (lineValues k)

theorem lineValues_homogeneous (i : Index) : (lineValues k i).IsHomogeneous 1 := by
  rcases i with j | u
  · fin_cases j
    · simpa [lineValues] using isHomogeneous_zero LineIndex k 1
    · exact isHomogeneous_X k _
  · exact isHomogeneous_X k _

noncomputable def lineGradedHom : grading k →+*ᵍ lineGrading k where
  toRingHom := (lineSpecialization k).toRingHom
  map_mem := by
    intro i P hP
    have h := ((mem_homogeneousSubmodule _ _).mp hP).aeval (lineValues k) (lineValues_homogeneous k)
    rw [one_mul] at h
    exact (mem_homogeneousSubmodule _ _).mpr h

@[simp] theorem lineGradedHom_apply (P : Coordinates k) :
    lineGradedHom k P = lineSpecialization k P := rfl

theorem lineGradedHom_irrelevant :
    HomogeneousIdeal.irrelevant (lineGrading k) ≤
      (HomogeneousIdeal.irrelevant (grading k)).map (lineGradedHom k) := by
  intro P hP
  have h := (Pcf.paperPIrrelevant_le_coordinateIdeal (K := k) (n := 1)) hP
  change P ∈ Ideal.span (Set.range (X : LineIndex → LineCoords k)) at h
  change P ∈ ((HomogeneousIdeal.irrelevant (grading k)).toIdeal.map (lineGradedHom k))
  refine (Ideal.span_le.mpr ?_) h
  rintro _ ⟨b, rfl⟩
  have hmem : ∀ i : Index,
      (X i : Coordinates k) ∈ (HomogeneousIdeal.irrelevant (grading k)).toIdeal :=
    fun i => HomogeneousIdeal.mem_irrelevant_of_mem (grading k) Nat.zero_lt_one
      (isHomogeneous_X k i)
  rcases b with j | u
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    have := Ideal.mem_map_of_mem (lineGradedHom k) (hmem (Sum.inl 1))
    simpa [lineSpecialization, lineValues, lu] using this
  · have := Ideal.mem_map_of_mem (lineGradedHom k) (hmem (Sum.inr ()))
    simpa [lineSpecialization, lineValues, lv] using this

/-- The actual linear embedding `[u:v] ↦ [0:u:v]` of the projective line. -/
noncomputable def lineEmbedding : Proj (lineGrading k) ⟶ Proj (grading k) :=
  Proj.map (lineGradedHom k) (lineGradedHom_irrelevant k)


/-- The graded section `u ↦ y, v ↦ z`. -/
noncomputable def lineSection : LineCoords k →ₐ[k] Coordinates k :=
  aeval (fun b => match b with
    | Sum.inl _ => y k
    | Sum.inr _ => z k)

theorem lineSpecialization_lineSection (P : LineCoords k) :
    lineSpecialization k (lineSection k P) = P := by
  have h : (lineSpecialization k).comp (lineSection k) = AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    intro b
    rcases b with j | u
    · have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      simp [lineSection, lineSpecialization, lineValues, y, lu]
    · simp [lineSection, lineSpecialization, lineValues, z, lv]
  exact congrArg (fun g : LineCoords k →ₐ[k] LineCoords k => g P) h

theorem lineSection_mem {n : ℕ} {P : LineCoords k} (hP : P ∈ lineGrading k n) :
    lineSection k P ∈ grading k n := by
  have h := ((mem_homogeneousSubmodule _ _).mp hP).aeval
    (fun b : LineIndex => match b with
      | Sum.inl _ => y k
      | Sum.inr _ => z k) (by
        intro b
        rcases b with j | u
        · exact isHomogeneous_X k _
        · exact isHomogeneous_X k _)
  rw [one_mul] at h
  exact (mem_homogeneousSubmodule _ _).mpr h

theorem awayMap_surjective {s : Coordinates k} {m : ℕ} (hs : s ∈ grading k m) :
    Function.Surjective (Away.map (lineGradedHom k) s) := by
  intro w
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective (lineGrading k)
    ((lineGradedHom k).map_mem hs) w
  refine ⟨Away.mk (grading k) hs n (lineSection k b) (lineSection_mem k hb), ?_⟩
  rw [Away.map_mk]
  congr 1
  exact lineSpecialization_lineSection k b

theorem isEmpty_preimage_x :
    IsEmpty (lineEmbedding k ⁻¹ᵁ Proj.basicOpen (grading k) (X (Sum.inl 0))) := by
  constructor
  rintro ⟨q, hq⟩
  change lineGradedHom k (X (Sum.inl 0)) ∉ q.asHomogeneousIdeal at hq
  apply hq
  simp [lineSpecialization, lineValues]

theorem lineEmbedding_preimage_basicOpen (s : Coordinates k) :
    lineEmbedding k ⁻¹ᵁ Proj.basicOpen (grading k) s =
      Proj.basicOpen (lineGrading k) (lineGradedHom k s) := rfl

/-- On each source chart the linear embedding is `Spec` of the chart pullback. -/
theorem lineEmbedding_restrict_square {s : Coordinates k} (hs : s ∈ grading k 1) :
    (Proj.basicOpenIsoSpec (lineGrading k) _ ((lineGradedHom k).map_mem hs) Nat.zero_lt_one).inv ≫
      (Scheme.isoOfEq _ (lineEmbedding_preimage_basicOpen k s)).inv ≫
      (lineEmbedding k ∣_ Proj.basicOpen (grading k) s) =
    Spec.map (CommRingCat.ofHom (Away.map (lineGradedHom k) s)) ≫
      (Proj.basicOpenIsoSpec (grading k) s hs Nat.zero_lt_one).inv := by
  rw [← cancel_mono (Proj.basicOpen (grading k) s).ι]
  simp only [Category.assoc, morphismRestrict_ι, Proj.basicOpenIsoSpec_inv_ι]
  rw [Scheme.isoOfEq_inv_ι_assoc, ← Category.assoc]
  exact Proj.awayι_comp_map (lineGradedHom k) (lineGradedHom_irrelevant k)
    Nat.zero_lt_one s hs

/-- The linear embedding is an actual closed immersion: the closed-immersion part of
Stacks Lemma 01N0 for the graded specialization to `H₀`.

Divergence from Stacks: only assertion (2) is proved, for this one graded map, which
is surjective in every degree; the assertion `U(ψ) = Y` is implicit in Mathlib's
`Proj.map` hypothesis and the twisting-sheaf assertion (3) is not stated.

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
@[stacks 01N0 "closed-immersion part, specialization to H₀"]
theorem lineEmbedding_isClosedImmersion : IsClosedImmersion (lineEmbedding k) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun i : Index => Proj.basicOpen (grading k) (X i))
    (Pcf.paperPSourceCoordinates_basicOpen_cover (K := k) (n := 2))
  intro i
  by_cases hx : i = Sum.inl 0
  · subst hx
    have := isEmpty_preimage_x k
    infer_instance
  have hs : (X i : Coordinates k) ∈ grading k 1 := isHomogeneous_X k i
  have hφs := (lineGradedHom k).map_mem hs
  let α := (Scheme.isoOfEq _ (lineEmbedding_preimage_basicOpen k (X i))) ≪≫
    Proj.basicOpenIsoSpec (lineGrading k) _ hφs Nat.zero_lt_one
  let β := Proj.basicOpenIsoSpec (grading k) _ hs Nat.zero_lt_one
  let S := Spec.map (CommRingCat.ofHom (Away.map (lineGradedHom k) (X i)))
  have hsq : α.inv ≫ (lineEmbedding k ∣_ Proj.basicOpen (grading k) (X i)) = S ≫ β.inv := by
    simp only [α, Iso.trans_inv, Category.assoc]
    exact lineEmbedding_restrict_square k hs
  have w : (lineEmbedding k ∣_ Proj.basicOpen (grading k) (X i)) ≫ β.hom = α.hom ≫ S := by
    calc (lineEmbedding k ∣_ Proj.basicOpen (grading k) (X i)) ≫ β.hom
        = (α.hom ≫ α.inv ≫ (lineEmbedding k ∣_ Proj.basicOpen (grading k) (X i))) ≫ β.hom := by
          simp
      _ = (α.hom ≫ S ≫ β.inv) ≫ β.hom := by rw [hsq]
      _ = α.hom ≫ S := by simp
  have e := Arrow.isoMk α β (f := Arrow.mk (lineEmbedding k ∣_ Proj.basicOpen (grading k) (X i)))
    (g := Arrow.mk S) w.symm
  exact (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion e).mpr
    (IsClosedImmersion.spec_of_surjective _ (awayMap_surjective k hs))


/-! ### The projective-line return -/

/-- The homogenized return `[u^(p+1) + c v^(p+1) : v^(p+1)]` on `H₀`. -/
noncomputable def lineForms : LineIndex → LineCoords k
  | Sum.inl _ => lu k ^ (p + 1) + C c * lv k ^ (p + 1)
  | Sum.inr _ => lv k ^ (p + 1)

theorem lineForms_homogeneous (i : LineIndex) : (lineForms k p c i).IsHomogeneous (p + 1) := by
  have hu : (lu k).IsHomogeneous 1 := isHomogeneous_X k _
  have hv : (lv k).IsHomogeneous 1 := isHomogeneous_X k _
  have hup : (lu k ^ (p + 1)).IsHomogeneous (p + 1) := by simpa using hu.pow (p + 1)
  have hvp : (lv k ^ (p + 1)).IsHomogeneous (p + 1) := by simpa using hv.pow (p + 1)
  rcases i with _ | _
  · simpa [lineForms] using hup.add (by simpa using (isHomogeneous_C LineIndex c).mul hvp)
  · simpa [lineForms] using hvp

theorem lineForms_cover : Pcf.PaperPFormsCoverProjective (lineForms k p c) := by
  apply (Pcf.paperPIrrelevant_le_coordinateIdeal (K := k) (n := 1)).trans
  change Ideal.span (Set.range (X : LineIndex → LineCoords k)) ≤
    (Ideal.span (Set.range (lineForms k p c))).radical
  rw [Ideal.span_le, Set.range_subset_iff]
  intro i
  apply Ideal.mem_radical_iff.mpr
  refine ⟨p + 1, ?_⟩
  have h0 : lineForms k p c (Sum.inl 0) ∈ Ideal.span (Set.range (lineForms k p c)) :=
    Ideal.subset_span ⟨Sum.inl 0, rfl⟩
  have h1 : lineForms k p c (Sum.inr ()) ∈ Ideal.span (Set.range (lineForms k p c)) :=
    Ideal.subset_span ⟨Sum.inr (), rfl⟩
  rcases i with j | u
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    have hh := Ideal.sub_mem _ h0 (Ideal.mul_mem_left _ (C c) h1)
    simpa [lineForms, lu] using hh
  · simpa [lineForms, lv] using h1

/-- The actual projective-line scheme morphism of the return. -/
noncomputable def lineReturnMap : Proj (lineGrading k) ⟶ Proj (lineGrading k) :=
  Pcf.paperPFormsProjectiveSchemeMap (lineForms k p c) (p + 1) (by omega)
    (lineForms_homogeneous k p c) (lineForms_cover k p c)

theorem algHom_ext_xyz_line {f g : Coordinates k →ₐ[k] LineCoords k}
    (hx : f (x k) = g (x k)) (hy : f (y k) = g (y k)) (hz : f (z k) = g (z k)) : f = g := by
  apply MvPolynomial.algHom_ext
  intro i
  rcases i with j | u
  · fin_cases j
    · exact hx
    · exact hy
  · exact hz

/-- Restriction of forms commutes with specialization to `H₀`. -/
theorem lineSpecialization_comp_forms (hp : 0 < p) :
    (lineSpecialization k).comp (aeval (forms k p c)) =
      (aeval (lineForms k p c)).comp (lineSpecialization k) := by
  apply algHom_ext_xyz_line
  · rw [AlgHom.comp_apply, AlgHom.comp_apply]
    have : aeval (forms k p c) (x k) = forms k p c (Sum.inl 0) := by simp [x]
    rw [this, forms_zero]
    simp [lineSpecialization, lineValues, x, y, zero_pow (by omega : p ≠ 0)]
  · rw [AlgHom.comp_apply, AlgHom.comp_apply]
    have : aeval (forms k p c) (y k) = forms k p c (Sum.inl 1) := by simp [y]
    rw [this, forms_one]
    simp [lineSpecialization, lineValues, lineForms, x, y, z, lu, lv, zero_pow (by omega : p ≠ 0),
      zero_pow (by omega : p + 1 ≠ 0)]
  · rw [AlgHom.comp_apply, AlgHom.comp_apply]
    have : aeval (forms k p c) (z k) = forms k p c (Sum.inr ()) := by simp [z]
    rw [this, forms_two]
    simp [lineSpecialization, lineValues, lineForms, z, lv]

/-- Identity cast between homogeneous localizations at equal elements. -/
noncomputable def awayCast {f g : LineCoords k} (h : f = g) :
    Away (lineGrading k) g →+* Away (lineGrading k) f :=
  Pcf.paperPDegreeLocalizationMap (𝒜 := lineGrading k) (ℬ := lineGrading k) (RingHom.id _) 1
    (fun m a ha => by simpa using ha) (by
      rintro _ ⟨n, rfl⟩
      exact ⟨n, by simp [h]⟩)

theorem awayι_cast {f g : LineCoords k} (h : f = g) {m : ℕ} (hf : f ∈ lineGrading k m)
    (hg : g ∈ lineGrading k m) (hm : 0 < m) :
    Proj.awayι (lineGrading k) f hf hm =
      Spec.map (CommRingCat.ofHom (awayCast k h)) ≫ Proj.awayι (lineGrading k) g hg hm := by
  subst h
  have : awayCast k (rfl : f = f) = RingHom.id _ := by
    ext w
    simp [awayCast, IsLocalization.map_id]
  rw [this]
  simp

theorem lineGradedHom_forms (hp : 0 < p) (P : Coordinates k) :
    lineGradedHom k (aeval (forms k p c) P) = aeval (lineForms k p c) (lineGradedHom k P) :=
  congrArg (fun f : Coordinates k →ₐ[k] LineCoords k => f P) (lineSpecialization_comp_forms k p c hp)

theorem lineGradedHom_z : lineGradedHom k (z k) = lv k := by
  simp [lineSpecialization, lineValues, z]

theorem lineChart_ne_zero :
    aeval (lineForms k p c) (lineGradedHom k (z k)) ≠ 0 := by
  rw [lineGradedHom_z]
  simp only [lv, aeval_X, lineForms]
  exact pow_ne_zero _ (X_ne_zero _)

omit [Field k] in
/-- The chart pullback of a homogeneous fraction `a / P^n`. -/
theorem paperPFormsAwayMap_mk {K : Type*} [Field K] {N : ℕ}
    (F : Fin N ⊕ Unit → MvPolynomial (Fin N ⊕ Unit) K) (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d)
    {P : MvPolynomial (Fin N ⊕ Unit) K} {m : ℕ}
    (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin N ⊕ Unit) K m) (n : ℕ)
    (a : MvPolynomial (Fin N ⊕ Unit) K)
    (ha : a ∈ MvPolynomial.homogeneousSubmodule (Fin N ⊕ Unit) K (n • m)) :
    Pcf.paperPFormsAwayMap F d hF P (Away.mk _ hP n a ha) =
      Away.mk _ (Pcf.paperPForms_degreeMap F d hF m P hP) n (aeval F a) (by
        have h := Pcf.paperPForms_degreeMap F d hF _ a ha
        have e : d * (n • m) = n • (d * m) := by
          simp only [smul_eq_mul]
          ring
        rwa [e] at h) := by
  apply val_injective
  simp [Pcf.paperPFormsAwayMap, Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk']

/-- The restriction of the actual global map along `ι` is the actual line return. -/
theorem lineEmbedding_comp_schemeMap (hp : 0 < p) :
    lineEmbedding k ≫ schemeMap k p c hp = lineReturnMap k p c ≫ lineEmbedding k := by
  have hz : z k ∈ grading k 1 := isHomogeneous_X k _
  have hφz : lineGradedHom k (z k) ∈ lineGrading k 1 := (lineGradedHom k).map_mem hz
  have hFz : aeval (forms k p c) (z k) ∈ grading k ((p + 1) * 1) :=
    Pcf.paperPForms_degreeMap (forms k p c) (p + 1) (forms_homogeneous k p c) 1 _ hz
  have hf₀ : aeval (lineForms k p c) (lineGradedHom k (z k)) ∈ lineGrading k ((p + 1) * 1) :=
    Pcf.paperPForms_degreeMap (lineForms k p c) (p + 1) (lineForms_homogeneous k p c) 1 _ hφz
  have hφFz := (lineGradedHom k).map_mem hFz
  have heq := (lineGradedHom_forms k p c hp (z k)).symm
  have hpos : 0 < (p + 1) * 1 := Nat.mul_pos (by omega) Nat.zero_lt_one
  let j := Proj.awayι (lineGrading k) _ hf₀ hpos
  haveI : IsDominant j := by
    constructor
    have hr : Set.range j = (Proj.basicOpen (lineGrading k)
        (aeval (lineForms k p c) (lineGradedHom k (z k))) : Set (Proj (lineGrading k))) := by
      rw [← Proj.opensRange_awayι (lineGrading k) _ hf₀ hpos]
      rfl
    change Dense (Set.range j)
    rw [hr]
    apply IsOpen.dense (Proj.basicOpen (lineGrading k) _).isOpen
    refine ⟨Pcf.paperPProjectiveGenericPoint (K := k) (n := 1), ?_⟩
    change _ ∉ (⊥ : Ideal (LineCoords k))
    intro h
    exact lineChart_ne_zero k p c ((Submodule.mem_bot _).mp h)
  apply ext_of_isDominant j
  have hR := Pcf.paperPForms_awayι_comp_map (lineForms k p c) (p + 1) (by omega)
    (lineForms_homogeneous k p c) (lineForms_cover k p c) Nat.zero_lt_one
    (lineGradedHom k (z k)) hφz
  have hι := Proj.awayι_comp_map (lineGradedHom k) (lineGradedHom_irrelevant k)
    Nat.zero_lt_one (z k) hz
  have hcast := awayι_cast k heq hf₀ hφFz hpos
  have hι2 := Proj.awayι_comp_map (lineGradedHom k) (lineGradedHom_irrelevant k)
    hpos (aeval (forms k p c) (z k)) hFz
  have hF := Pcf.paperPForms_awayι_comp_map (forms k p c) (p + 1) (by omega)
    (forms_homogeneous k p c) (forms_cover k p c hp) Nat.zero_lt_one (z k) hz
  change j ≫ Proj.map _ _ ≫ Pcf.paperPFormsProjectiveSchemeMap _ _ _ _ _ =
    j ≫ Pcf.paperPFormsProjectiveSchemeMap _ _ _ _ _ ≫ Proj.map _ _
  rw [← Category.assoc j, ← Category.assoc j]
  change (Proj.awayι (lineGrading k) _ hf₀ hpos ≫ _) ≫ _ = (Proj.awayι (lineGrading k) _ hf₀ hpos ≫ _) ≫ _
  rw [hR, hcast]
  simp only [Category.assoc]
  rw [reassoc_of% hι2, hF, hι]
  simp only [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext w
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (grading k) hz w
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply]
  rw [paperPFormsAwayMap_mk, Away.map_mk, Away.map_mk, paperPFormsAwayMap_mk]
  have h1 : ∀ P, lineSpecialization k (bind₁ (forms k p c) P) =
      bind₁ (lineForms k p c) (lineSpecialization k P) := fun P => by
    simpa [aeval_eq_bind₁] using lineGradedHom_forms k p c hp P
  simp [awayCast, Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk']
  simp only [h1]

end Pcf.Examples.PaperP.Wild
