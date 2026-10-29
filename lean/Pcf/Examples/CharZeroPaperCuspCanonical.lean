/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.CharZeroPaperCuspBranch
public import Pcf.Examples.CharZeroPaperSmoothBranch
public import Pcf.PaperCharZero.SupportingAffineNormalization
public import Pcf.Stacks.Common.RegularNormal

/-!
# Canonical normalization and branch loci for `paper.tex`, Example `ex:cusp`

The explicit integral-closure normalization of the monomial cusp from
`CharZeroPaperCuspGeometry` is identified with the project's canonical
generic-stalk normalization `Palomar.normalization`. Consequently the
parametrization `g(t) = (t², t³)` is the canonical normalization of the cusp,
its canonical normalized lift is an isomorphism, and its normalized branch
support is empty.

The ambient map `f(u,v) = (u², u³+v)` is the squaring map of
`ex:smooth-restriction` precomposed with the source shear `(u,v) ↦ (u, v+u³)`
and conjugated by the coordinate swap. Its actual normalized branch support is
`V(x)`, which meets the actual closed cusp exactly at the origin; the cusp local
ring at the origin is not regular. Hence the strict inclusion
`Branch(g) = ∅ ⊊ B ∩ Z` holds for actual schemes and canonical normalizations.
No branch, normalization, or regularity assertion is an input.
-/

@[expose] public section
noncomputable section

namespace Pcf.Examples.CharZeroPaperCuspCanonical

open CategoryTheory AlgebraicGeometry Polynomial
open CharZeroPaperCuspGeometry CharZeroPaperCuspBranch Pcf.PaperCharZero

universe u
variable (k : Type u) [Field k]

/-! ### The canonical normalization of the cusp -/

/-- The explicit affine normalization of the cusp is the canonical one, over the cusp. -/
def cuspNormalizationIso : affineNormalization k ≅ Palomar.normalization (cusp k) :=
  affineNormalizationIso (.of (CuspRing k)) (FunctionField k)

theorem cuspNormalizationIso_comm :
    (cuspNormalizationIso k).hom ≫ Palomar.normalizationMap (cusp k) =
      affineNormalizationProjection k :=
  affineNormalizationIso_hom_normalizationMap _ _

/-- `paper.tex`, `ex:cusp`: "`g` is the normalization of `B`". The parameter
line is isomorphic to the canonical normalization of the actual cusp, and under
this isomorphism the canonical normalization map is the parametrization. -/
def parameterLineNormalizationIso : parameterLine k ≅ Palomar.normalization (cusp k) :=
  normalizationIso k ≪≫ cuspNormalizationIso k

theorem parameterLineNormalizationIso_comm :
    (parameterLineNormalizationIso k).hom ≫ Palomar.normalizationMap (cusp k) =
      parametrization k := by
  simp only [parameterLineNormalizationIso, Iso.trans_hom, Category.assoc,
    cuspNormalizationIso_comm, normalizationIso, asIso_hom, normalization_square]

instance parameterLine_isNormal : IsNormalScheme (parameterLine k) :=
  CharZeroPaperSmoothBranch.normal_spec _

/-- The canonical normalized lift of the parametrization is `ν_{A¹}` followed by
the identification of `A¹` with the canonical normalization of the cusp. -/
theorem normalized_parametrization_eq :
    schemeGlobalNormalizationMorphism (parametrization k) =
      Palomar.normalizationMap (parameterLine k) ≫ (parameterLineNormalizationIso k).hom :=
  schemeGlobalNormalizationMorphism_eq_of_factor _ _ _ (parameterLineNormalizationIso_comm k)

/-- `ex:cusp`: the lift of `g` to the canonical normalizations is an isomorphism
(the identity of `𝔸¹` after the canonical identifications). -/
theorem normalized_parametrization_isIso :
    IsIso (schemeGlobalNormalizationMorphism (parametrization k)) :=
  schemeGlobalNormalizationMorphism_isIso_of_factor _ _ _ (parameterLineNormalizationIso_comm k)

instance parameterLine_normalization_isIso : IsIso (Palomar.normalizationMap (parameterLine k)) :=
  normalScheme_normalizationMap_isIso _

/-- `ex:cusp`: "its lift to normalizations is the identity of `𝔸¹`". After the
canonical identifications `ν_{𝔸¹}` and `parameterLineNormalizationIso`, the
canonical normalized lift of `g` is the identity of the parameter line. -/
theorem normalized_parametrization_identity :
    inv (Palomar.normalizationMap (parameterLine k)) ≫
        schemeGlobalNormalizationMorphism (parametrization k) ≫
          (parameterLineNormalizationIso k).inv = 𝟙 _ := by
  rw [normalized_parametrization_eq]
  simp

/-- `ex:cusp`: `Branch(g) = ∅` for the actual canonical normalized branch support. -/
theorem normalized_parametrization_branch_empty :
    normalizedMorphismBranchSupport (parametrization k) = ∅ :=
  normalizedMorphismBranchSupport_empty_of_factor _ _ _ (parameterLineNormalizationIso_comm k)

/-! ### The ambient map as a sheared squaring map -/

/-- Pullback along the target coordinate identification `k[x,y] ≅ k[y][x]`. -/
def targetChange : CharZeroPaperSmoothRestriction.plane k ⟶ plane k :=
  Spec.map (CommRingCat.ofHom (targetCoordinates k).toRingHom)

/-- The source shear followed by the inverse coordinate identification. -/
def sourceRingChange : CharZeroPaperSmoothRestriction.PlaneRing k →+* MvPolynomial (Fin 2) k :=
  (shearEquiv k).toRingHom.comp (targetCoordinates k).symm.toRingHom

def sourceChange : plane k ⟶ CharZeroPaperSmoothRestriction.plane k :=
  Spec.map (CommRingCat.ofHom (sourceRingChange k))

instance targetChange_isIso : IsIso (targetChange k) :=
  (Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso (targetCoordinates k).toRingEquiv).op).isIso_hom

instance sourceChange_isIso : IsIso (sourceChange k) :=
  (Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
    ((targetCoordinates k).symm.toRingEquiv.trans (shearEquiv k).toRingEquiv)).op).isIso_hom

theorem targetCoordinates_symm_x : (targetCoordinates k).symm X = MvPolynomial.X 0 := by
  rw [AlgEquiv.symm_apply_eq, targetCoordinates_x]

theorem targetCoordinates_symm_y : (targetCoordinates k).symm (C X) = MvPolynomial.X 1 := by
  rw [AlgEquiv.symm_apply_eq, targetCoordinates_y]

theorem targetCoordinates_C (a : k) :
    (targetCoordinates k) (MvPolynomial.C a) = C (C a) :=
  (targetCoordinates k).commutes a

/-- The displayed ring map `(u,v) ↦ (u², u³+v)` factors through squaring. -/
theorem ambient_pullback_factor :
    (MvPolynomial.aeval (Cusp.cuspSource k)).toRingHom =
      (sourceRingChange k).comp ((CharZeroPaperSmoothRestriction.ambientPullback k).comp
        (targetCoordinates k).toRingHom) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    have h2 : (targetCoordinates k).symm (C (C a)) = MvPolynomial.C a := by
      rw [← targetCoordinates_C, AlgEquiv.symm_apply_apply]
    change MvPolynomial.aeval _ (MvPolynomial.C a) = sourceRingChange k
      (CharZeroPaperSmoothRestriction.ambientPullback k ((targetCoordinates k) (MvPolynomial.C a)))
    rw [targetCoordinates_C, CharZeroPaperSmoothRestriction.ambientPullback_C,
      MvPolynomial.aeval_C]
    simp only [sourceRingChange, RingHom.coe_comp, Function.comp_apply]
    erw [h2]
    exact ((shearEquiv k).commutes a).symm
  · intro i
    fin_cases i
    · simp [sourceRingChange, shearEquiv, shearPullback, Cusp.cuspSource,
        targetCoordinates_symm_x]
    · simp [sourceRingChange, shearEquiv, shearPullback, Cusp.cuspSource,
        targetCoordinates_symm_y]
      ring

/-- The actual ambient map is `sourceChange ≫ squaring ≫ targetChange`. -/
theorem ambientMap_factor :
    ambientMap k = sourceChange k ≫ CharZeroPaperSmoothRestriction.ambientMap k ≫
      targetChange k := by
  simp only [ambientMap, sourceChange, targetChange, CharZeroPaperSmoothRestriction.ambientMap,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact ambient_pullback_factor k

/-! ### The actual normalized ambient branch support is `V(x)` -/

attribute [local instance] CharZeroPaperSmoothRestriction.ambient_finite
  CharZeroPaperSmoothRestriction.ambient_surjective

instance ambientMap_finite : IsFinite (ambientMap k) := by
  rw [ambientMap_factor]; infer_instance

instance ambientMap_surjective : Surjective (ambientMap k) := by
  rw [ambientMap_factor]; infer_instance

instance plane_isNormal : IsNormalScheme (plane k) :=
  CharZeroPaperSmoothBranch.normal_spec _

set_option backward.isDefEq.respectTransparency false in
theorem targetChange_image_axis :
    targetChange k '' {p : CharZeroPaperSmoothRestriction.plane k |
        (X : CharZeroPaperSmoothRestriction.PlaneRing k) ∈ p.asIdeal} =
      {q : plane k | MvPolynomial.X 0 ∈ q.asIdeal} := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    change MvPolynomial.X 0 ∈ Ideal.comap (targetCoordinates k).toRingHom p.asIdeal
    rw [Ideal.mem_comap]
    simpa [targetCoordinates_x] using hp
  · intro hq
    refine ⟨PrimeSpectrum.comap (targetCoordinates k).symm.toRingHom q, ?_, ?_⟩
    · change X ∈ Ideal.comap (targetCoordinates k).symm.toRingHom q.asIdeal
      rw [Ideal.mem_comap]
      simpa [targetCoordinates_symm_x] using hq
    · apply PrimeSpectrum.ext
      change Ideal.comap (targetCoordinates k).toRingHom
        (Ideal.comap (targetCoordinates k).symm.toRingHom q.asIdeal) = q.asIdeal
      ext r
      simp

/-- The actual codimension-one nonreduced-fibre support of `f` is the axis `x = 0`. -/
theorem ambient_reducedFiberBranch_support [CharZero k] :
    divisorSupport (schemeReducedFiberBranch (ambientMap k)) =
      {q : plane k | MvPolynomial.X 0 ∈ q.asIdeal} := by
  rw [ambientMap_factor, reducedFiberBranch_support_tower, reducedFiberBranch_support_tower,
    reducedFiberBranch_empty_of_isIso (sourceChange k),
    reducedFiberBranch_empty_of_isIso (targetChange k),
    CharZeroPaperSmoothBranch.ambient_reducedFiberBranch_support, targetChange_image_axis]
  simp [divisorSupport]

/-- `ex:cusp`: the manuscript's (normalized) branch support of the actual ambient map
`f(u,v) = (u², u³+v)` is `V(x)`. -/
theorem normalized_ambient_branch [CharZero k] :
    normalizedMorphismBranchSupport (ambientMap k) =
      {q : plane k | MvPolynomial.X 0 ∈ q.asIdeal} := by
  rw [CharZeroPaperSmoothBranch.normalized_support_eq_reduced_support,
    ambient_reducedFiberBranch_support]

/-! ### The origin and the intersection `B ∩ Z` -/

/-- The ideal of the origin `(0,0)` of the plane. -/
def planeOriginIdeal : Ideal (MvPolynomial (Fin 2) k) :=
  RingHom.ker (MvPolynomial.eval (0 : Fin 2 → k))

instance planeOriginIdeal_isMaximal : (planeOriginIdeal k).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun a => ⟨MvPolynomial.C a, by simp⟩

/-- The origin of the actual plane, as a scheme point. -/
def planeOrigin : plane k := ⟨planeOriginIdeal k, inferInstance⟩

theorem planeOriginIdeal_le {q : Ideal (MvPolynomial (Fin 2) k)}
    (h0 : MvPolynomial.X 0 ∈ q) (h1 : MvPolynomial.X 1 ∈ q) : planeOriginIdeal k ≤ q := by
  intro p hp
  have hp0 : MvPolynomial.constantCoeff p = 0 := by
    rw [← MvPolynomial.eval_zero]; exact hp
  have hspan : p ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin 2))) := by
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      have h := hp0
      rw [MvPolynomial.constantCoeff_eq] at h
      exact (MvPolynomial.mem_support_iff.mp hm) h
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
    exact ⟨i, Set.mem_univ _, by simpa using hi⟩
  refine (Ideal.span_le.mpr ?_) hspan
  rintro _ ⟨i, -, rfl⟩
  fin_cases i
  · exact h0
  · exact h1

theorem X_mem_planeOriginIdeal (i : Fin 2) : MvPolynomial.X i ∈ planeOriginIdeal k := by
  simp [planeOriginIdeal]

/-- `ex:cusp`: the actual closed cusp `B` meets the actual normalized ambient branch
support `Z = V(x)` exactly at the origin. -/
theorem cusp_inter_normalized_ambient_branch [CharZero k] :
    Set.range (cuspImmersion k) ∩ normalizedMorphismBranchSupport (ambientMap k) =
      {planeOrigin k} := by
  rw [normalized_ambient_branch]
  ext q
  simp only [Set.mem_inter_iff, mem_cusp_range_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hc, hx⟩
    have hy2 : MvPolynomial.X 1 ^ 2 ∈ q.asIdeal := by
      have := q.asIdeal.add_mem hc (q.asIdeal.mul_mem_left (MvPolynomial.X 0 ^ 2) hx)
      convert this using 1; ring
    have hy : MvPolynomial.X 1 ∈ q.asIdeal := q.isPrime.mem_of_pow_mem 2 hy2
    have hle := planeOriginIdeal_le k hx hy
    exact PrimeSpectrum.ext
      ((planeOriginIdeal_isMaximal k).eq_of_le q.isPrime.ne_top hle).symm
  · rintro rfl
    refine ⟨?_, X_mem_planeOriginIdeal k 0⟩
    simp [planeOrigin, planeOriginIdeal]

/-- `ex:cusp`: `Branch(f) = V(x)` is not the cusp `B`; the point `(1,1)` lies on
`B` but not on `V(x)`. -/
theorem normalized_ambient_branch_ne_cusp [CharZero k] :
    normalizedMorphismBranchSupport (ambientMap k) ≠ Set.range (cuspImmersion k) := by
  let I : Ideal (MvPolynomial (Fin 2) k) := RingHom.ker (MvPolynomial.eval (fun _ => (1 : k)))
  have hI : I.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun a => ⟨MvPolynomial.C a, by simp⟩
  let q : plane k := ⟨I, hI.isPrime⟩
  intro h
  have hq : q ∈ Set.range (cuspImmersion k) := by
    rw [mem_cusp_range_iff]
    simp [q, I]
  rw [← h, normalized_ambient_branch] at hq
  have hx : MvPolynomial.X 0 ∈ RingHom.ker (MvPolynomial.eval (fun _ : Fin 2 => (1 : k))) := hq
  rw [RingHom.mem_ker, MvPolynomial.eval_X] at hx
  exact one_ne_zero hx

/-! ### The origin is a singular point of the cusp -/

/-- The ideal of the origin `t = 0` in the cusp coordinate ring `k[t²,t³]`. -/
def cuspOriginIdeal : Ideal (CuspRing k) :=
  RingHom.ker ((Polynomial.evalRingHom (0 : k)).comp (CuspRing k).val.toRingHom)

instance cuspOriginIdeal_isMaximal : (cuspOriginIdeal k).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun a => ⟨algebraMap k (CuspRing k) a, by simp⟩

/-- The origin of the actual cusp, as a scheme point. -/
def cuspOrigin : cusp k := ⟨cuspOriginIdeal k, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-- The cusp origin is the plane origin. -/
theorem cuspImmersion_cuspOrigin : cuspImmersion k (cuspOrigin k) = planeOrigin k := by
  apply PrimeSpectrum.ext
  change Ideal.comap (cuspCoordinateMap k).toRingHom (cuspOriginIdeal k) = planeOriginIdeal k
  rw [cuspOriginIdeal, planeOriginIdeal, RingHom.comap_ker]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro a; simp [cuspCoordinateMap, planeParamPullback]
  · intro i; fin_cases i <;> simp [cuspCoordinateMap, planeParamPullback]

/-- Any localization of the cusp ring at the origin is not integrally closed:
`t = t³/t²` is integral over it but does not lie in it. -/
theorem cuspOrigin_localization_not_integrallyClosed
    (S : Type u) [CommRing S] [Algebra (CuspRing k) S]
    [IsLocalization.AtPrime S (cuspOriginIdeal k)] :
    ¬ IsIntegrallyClosed S := by
  intro hic
  let m := cuspOriginIdeal k
  have hle : m.primeCompl ≤ nonZeroDivisors (CuspRing k) := m.primeCompl_le_nonZeroDivisors
  let : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors (S := S) hle
  have hinj : Function.Injective (algebraMap (CuspRing k) S) := IsLocalization.injective S hle
  have hLF : Function.Injective (algebraMap S (FractionRing S)) := IsFractionRing.injective _ _
  let F := FractionRing S
  let a0 : CuspRing k := ⟨X ^ 2, Cusp.X_sq_mem k⟩
  let b0 : CuspRing k := ⟨X ^ 3, Cusp.X_cube_mem k⟩
  have hab : b0 * b0 = a0 * (a0 * a0) := Subtype.ext (by
    change (X ^ 3 * X ^ 3 : Polynomial k) = X ^ 2 * (X ^ 2 * X ^ 2); ring)
  have ha0 : a0 ≠ 0 := fun h => by
    have h' : (X ^ 2 : Polynomial k) = 0 := congrArg Subtype.val h
    exact pow_ne_zero 2 X_ne_zero h'
  let a : F := algebraMap S F (algebraMap (CuspRing k) S a0)
  let b : F := algebraMap S F (algebraMap (CuspRing k) S b0)
  have ha : a ≠ 0 := fun h => ha0 (hinj (hLF (by rw [map_zero, map_zero]; exact h)))
  let x : F := b / a
  have hx2 : x ^ 2 = algebraMap S F (algebraMap (CuspRing k) S a0) := by
    have hb : b * b = a * (a * a) := by
      simp only [b, a, ← map_mul, hab]
    simp only [x, pow_two]
    rw [div_mul_div_comm, div_eq_iff (mul_ne_zero ha ha), hb]
  have hint : IsIntegral S x := IsIntegral.of_pow (by norm_num : 0 < 2)
    (hx2 ▸ isIntegral_algebraMap)
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := S) (K := F)).mp hint
  have hya : y * algebraMap (CuspRing k) S a0 = algebraMap (CuspRing k) S b0 := by
    apply hLF
    rw [map_mul, hy]
    exact div_mul_cancel₀ b ha
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective m.primeCompl y
  have hrs : r * a0 = (s : CuspRing k) * b0 := by
    apply hinj
    have h := congrArg (· * algebraMap (CuspRing k) S s) hya
    simp only at h
    rw [mul_right_comm, IsLocalization.mk'_spec] at h
    rw [map_mul, map_mul, h, mul_comm]
  have hrs' : (r : Polynomial k) * X ^ 2 = (s : Polynomial k) * X * X ^ 2 := by
    have h := congrArg Subtype.val hrs
    change (r : Polynomial k) * X ^ 2 = (s : Polynomial k) * X ^ 3 at h
    rw [h]; ring
  have hr : (r : Polynomial k) = (s : Polynomial k) * X :=
    mul_right_cancel₀ (pow_ne_zero 2 X_ne_zero) hrs'
  have hr1 : (r : Polynomial k).coeff 1 = 0 := Cusp.coeff_one_eq_zero_of_mem k r.2
  rw [hr, Polynomial.coeff_mul_X] at hr1
  apply s.2
  change (Polynomial.evalRingHom (0 : k)) (s : Polynomial k) = 0
  rw [Polynomial.coe_evalRingHom, ← Polynomial.coeff_zero_eq_eval_zero]
  exact hr1

set_option backward.isDefEq.respectTransparency false in
/-- `ex:cusp`: `(0,0) ∈ Sing(B)`. The actual local ring of the cusp at the origin is
not a regular local ring. -/
theorem cuspOrigin_not_regular :
    ¬ IsRegularLocalRing ((cusp k).presheaf.stalk (cuspOrigin k)) := by
  intro hreg
  have hic := Pcf.Stacks.isIntegrallyClosed_of_isRegularLocalRing
    ((cusp k).presheaf.stalk (cuspOrigin k))
  let : IsLocalization.AtPrime
      ((AlgebraicGeometry.Spec.structureSheaf (CuspRing k)).presheaf.stalk (cuspOrigin k))
      (cuspOriginIdeal k) :=
    StructureSheaf.IsLocalization.to_stalk (CuspRing k) (cuspOrigin k)
  exact cuspOrigin_localization_not_integrallyClosed k
    ((AlgebraicGeometry.Spec.structureSheaf (CuspRing k)).presheaf.stalk (cuspOrigin k)) hic

/-! ### The strict inclusion -/

/-- `ex:cusp`: `Branch(g) = ∅ ⊊ B ∩ Z`, for the actual canonical normalized branch
supports, with both sides regarded as subsets of the ambient target plane. -/
theorem normalized_branch_strict_inclusion [CharZero k] :
    (cuspImmersion k) '' normalizedMorphismBranchSupport (parametrization k) ⊂
      Set.range (cuspImmersion k) ∩ normalizedMorphismBranchSupport (ambientMap k) := by
  rw [normalized_parametrization_branch_empty, Set.image_empty,
    cusp_inter_normalized_ambient_branch]
  exact Set.empty_ssubset.mpr ⟨planeOrigin k, rfl⟩

/-- The failure point of the strict inclusion is the singular point of `B`. -/
theorem strict_inclusion_point_singular :
    cuspImmersion k (cuspOrigin k) = planeOrigin k ∧
      ¬ IsRegularLocalRing ((cusp k).presheaf.stalk (cuspOrigin k)) :=
  ⟨cuspImmersion_cuspOrigin k, cuspOrigin_not_regular k⟩

end Pcf.Examples.CharZeroPaperCuspCanonical

#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.cuspNormalizationIso
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.cuspNormalizationIso_comm
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.parameterLineNormalizationIso
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.parameterLineNormalizationIso_comm
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.parameterLine_isNormal
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.normalized_parametrization_eq
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.normalized_parametrization_isIso
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.parameterLine_normalization_isIso
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.normalized_parametrization_identity
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.normalized_parametrization_branch_empty
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.targetChange
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.sourceRingChange
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.sourceChange
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.targetChange_isIso
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.sourceChange_isIso
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.targetCoordinates_symm_x
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.targetCoordinates_symm_y
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.targetCoordinates_C
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.ambient_pullback_factor
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.ambientMap_factor
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.ambientMap_finite
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.ambientMap_surjective
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.plane_isNormal
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.targetChange_image_axis
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.ambient_reducedFiberBranch_support
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.normalized_ambient_branch
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.planeOriginIdeal
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.planeOriginIdeal_isMaximal
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.planeOrigin
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.planeOriginIdeal_le
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.X_mem_planeOriginIdeal
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.cusp_inter_normalized_ambient_branch
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.normalized_ambient_branch_ne_cusp
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.cuspOriginIdeal
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.cuspOriginIdeal_isMaximal
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.cuspOrigin
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.cuspImmersion_cuspOrigin
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.cuspOrigin_localization_not_integrallyClosed
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.cuspOrigin_not_regular
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.normalized_branch_strict_inclusion
#print axioms Pcf.Examples.CharZeroPaperCuspCanonical.strict_inclusion_point_singular

#check @Pcf.Examples.CharZeroPaperCuspCanonical.normalized_parametrization_identity
#check @Pcf.Examples.CharZeroPaperCuspCanonical.normalized_parametrization_branch_empty
#check @Pcf.Examples.CharZeroPaperCuspCanonical.normalized_ambient_branch
#check @Pcf.Examples.CharZeroPaperCuspCanonical.cusp_inter_normalized_ambient_branch
#check @Pcf.Examples.CharZeroPaperCuspCanonical.cuspOrigin_not_regular
#check @Pcf.Examples.CharZeroPaperCuspCanonical.normalized_branch_strict_inclusion
#check @Pcf.Examples.CharZeroPaperCuspCanonical.normalized_ambient_branch_ne_cusp
#check @Pcf.Examples.CharZeroPaperCuspCanonical.parameterLineNormalizationIso_comm
