/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.Algebra.MvPolynomial.Expand
public import Pcf.Examples.Cusp
public import Pcf.Examples.CharZeroPaperSmoothBranch

/-!
# Actual cone and restricted-line schemes in `ex:branch-singular`

The ambient target is the manuscript's actual quotient by `xz-y²`.
We construct the finite morphism and its square with the two affine lines.
The restricted map has actual normalized branch support equal to the origin.
The cone parametrization is injective in characteristic zero, so the displayed
quotient is integral and the ambient scheme map is surjective. The cone's
normality, singular locus, and empty ambient branch remain open;
none is imposed as a hypothesis or inferred solely from coordinate calculations.
-/

@[expose] public section
noncomputable section
namespace Pcf.Examples.CharZeroPaperConeBranch
open CategoryTheory AlgebraicGeometry Polynomial Pcf.PaperCharZero
open scoped TensorProduct
universe u
variable (K : Type u) [Field K]

abbrev ConeRing := MvPolynomial (Fin 3) K ⧸ Cusp.coneIdeal K
abbrev SourceRing := MvPolynomial (Fin 2) K
abbrev cone : Scheme := Spec (.of (ConeRing K))
abbrev sourcePlane : Scheme := Spec (.of (SourceRing K))
abbrev line : Scheme := Spec (.of (Polynomial K))

/-- The actual morphism to the displayed quadric hypersurface. -/
def coneMap : sourcePlane K ⟶ cone K :=
  Spec.map (CommRingCat.ofHom (Cusp.coneParam K).toRingHom)

/-- Integrality uses the displayed coordinate squares, not a presumed quotient identification. -/
theorem coneParam_finite : (Cusp.coneParam K).toRingHom.Finite := by
  let : Algebra (ConeRing K) (SourceRing K) := (Cusp.coneParam K).toRingHom.toAlgebra
  let : IsScalarTower K (ConeRing K) (SourceRing K) := IsScalarTower.of_algHom (Cusp.coneParam K)
  have hx (i : Fin 2) : IsIntegral (ConeRing K) (MvPolynomial.X i : SourceRing K) := by
    apply IsIntegral.of_pow (n := 2) (by decide)
    have h := isIntegral_algebraMap (R := ConeRing K) (A := SourceRing K)
      (x := Ideal.Quotient.mk (Cusp.coneIdeal K) (MvPolynomial.X (if i = 0 then 0 else 2)))
    change IsIntegral (ConeRing K)
      ((MvPolynomial.aeval (Cusp.coneMap K)) (MvPolynomial.X (if i = 0 then 0 else 2))) at h
    fin_cases i <;> simpa [Cusp.coneMap] using h
  let : Algebra.IsIntegral (ConeRing K) (SourceRing K) := ⟨fun p => by
    induction p using MvPolynomial.induction_on with
    | C a => exact (isIntegral_algebraMap (R := K) (A := SourceRing K) (x := a)).tower_top
    | add p q hp hq => exact hp.add hq
    | mul_X p i hp => exact hp.mul (hx i)⟩
  let : Algebra.FiniteType (ConeRing K) (SourceRing K) :=
    Algebra.FiniteType.of_restrictScalars_finiteType K (ConeRing K) (SourceRing K)
  exact RingHom.finite_algebraMap.mpr Algebra.IsIntegral.finite

instance coneMap_finite : IsFinite (coneMap K) :=
  (IsFinite.SpecMap_iff _).mpr (coneParam_finite K)

/-- Pullback of the target line `B=V(y,z)`, parametrized by its x coordinate. -/
def targetLinePullback : ConeRing K →ₐ[K] Polynomial K :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval ![(X : Polynomial K), 0, 0]) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    simp)

theorem targetLinePullback_surjective : Function.Surjective (targetLinePullback K) := by
  intro p
  refine ⟨Ideal.Quotient.mk _ (Polynomial.aeval (MvPolynomial.X 0) p), ?_⟩
  change (MvPolynomial.aeval ![(X : Polynomial K), 0, 0])
    (Polynomial.aeval (MvPolynomial.X 0) p) = p
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp_all
  | monomial n a => simp [← C_mul_X_pow_eq_monomial]

def targetLine : line K ⟶ cone K :=
  Spec.map (CommRingCat.ofHom (targetLinePullback K).toRingHom)

instance targetLine_closedImmersion : IsClosedImmersion (targetLine K) :=
  IsClosedImmersion.spec_of_surjective _ (targetLinePullback_surjective K)

/-- The source line `A=V(v)` with its u parameter. -/
def sourceLinePullback : SourceRing K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![(X : Polynomial K), 0]

theorem sourceLinePullback_surjective : Function.Surjective (sourceLinePullback K) := by
  intro p
  refine ⟨Polynomial.aeval (MvPolynomial.X 0) p, ?_⟩
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp_all [sourceLinePullback]
  | monomial n a => simp [sourceLinePullback, ← C_mul_X_pow_eq_monomial]

def sourceLine : line K ⟶ sourcePlane K :=
  Spec.map (CommRingCat.ofHom (sourceLinePullback K).toRingHom)

instance sourceLine_closedImmersion : IsClosedImmersion (sourceLine K) :=
  IsClosedImmersion.spec_of_surjective _ (sourceLinePullback_surjective K)

def squarePullback : Polynomial K →+* Polynomial K := (Polynomial.expand K 2).toRingHom

def squareMap : line K ⟶ line K := Spec.map (CommRingCat.ofHom (squarePullback K))

theorem restriction_square :
    sourceLine K ≫ coneMap K = squareMap K ≫ targetLine K := by
  simp only [sourceLine, coneMap, squareMap, targetLine, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro p
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective p
  change sourceLinePullback K ((MvPolynomial.aeval (Cusp.coneMap K)) p) =
    squarePullback K ((MvPolynomial.aeval ![(X : Polynomial K), 0, 0]) p)
  have h : (sourceLinePullback K).comp (MvPolynomial.aeval (Cusp.coneMap K)) =
      (Polynomial.expand K 2).comp (MvPolynomial.aeval ![(X : Polynomial K), 0, 0]) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [sourceLinePullback, Cusp.coneMap]
  exact congrArg (fun f : MvPolynomial (Fin 3) K →ₐ[K] Polynomial K => f p) h

@[simp] theorem squarePullback_X : squarePullback K X = X ^ 2 := Polynomial.expand_X _
@[simp] theorem squarePullback_C (a : K) : squarePullback K (C a) = C a := Polynomial.expand_C _ _

/-- Squaring one variable is a finite ring map over any coefficient ring. -/
theorem squarePullback_finite : (squarePullback K).Finite := by
  let : Algebra (Polynomial K) (Polynomial K) := (squarePullback K).toAlgebra
  let : Module (Polynomial K) (Polynomial K) := (squarePullback K).toAlgebra.toModule
  have hx : IsIntegral (Polynomial K) (X : Polynomial K) := by
    apply IsIntegral.of_pow (n := 2) (by decide)
    rw [← squarePullback_X K]
    exact isIntegral_algebraMap
  have ha : Algebra.adjoin (Polynomial K) ({X} : Set (Polynomial K)) = ⊤ := by
    apply Algebra.eq_top_iff.mpr
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => exact add_mem hp hq
    | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial]
      apply mul_mem
      · have h := (Algebra.adjoin (Polynomial K) ({X} : Set (Polynomial K))).algebraMap_mem (C a)
        simpa only [RingHom.algebraMap_toAlgebra, squarePullback_C] using h
      · exact pow_mem (Algebra.subset_adjoin (Set.mem_singleton X)) n
  have hfg := hx.fg_adjoin_singleton
  rw [ha] at hfg
  exact Module.finite_def.mpr hfg


instance squareMap_finite : IsFinite (squareMap K) :=
  (IsFinite.SpecMap_iff _).mpr (squarePullback_finite K)

instance squareMap_surjective : Surjective (squareMap K) := by
  constructor
  exact (squarePullback_finite K).to_isIntegral.comap_surjective
    (Polynomial.expand_injective (by decide))

/-- A monic presentation of the square degree-two algebra. -/
def squareRelation : Polynomial (Polynomial K) := X ^ 2 - C X

def presentationToSource : AdjoinRoot (squareRelation K) →+* Polynomial K :=
  AdjoinRoot.lift (squarePullback K) X (by simp [squareRelation])

def sourceToPresentation : Polynomial K →+* AdjoinRoot (squareRelation K) :=
  Polynomial.eval₂RingHom ((AdjoinRoot.of (squareRelation K)).comp C)
    (AdjoinRoot.root (squareRelation K))

@[simp] theorem sourceToPresentation_C (p : K) :
    sourceToPresentation K (C p) = AdjoinRoot.of (squareRelation K) (C p) := by
  simp [sourceToPresentation]

@[simp] theorem sourceToPresentation_X :
    sourceToPresentation K X = AdjoinRoot.root (squareRelation K) := by
  simp [sourceToPresentation]

theorem presentation_root_sq :
    AdjoinRoot.root (squareRelation K) ^ 2 = AdjoinRoot.of (squareRelation K) X := by
  have h : eval₂ (AdjoinRoot.of (squareRelation K)) (AdjoinRoot.root (squareRelation K))
      (X ^ 2 - C (X : Polynomial K)) = 0 := AdjoinRoot.eval₂_root (squareRelation K)
  simpa only [ eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] using h

theorem presentationToSource_comp_source :
    (presentationToSource K).comp (sourceToPresentation K) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro p; simp [RingHom.comp_apply, presentationToSource]
  · simp [RingHom.comp_apply, presentationToSource]

theorem sourceToPresentation_comp_square :
    (sourceToPresentation K).comp (squarePullback K) = AdjoinRoot.of (squareRelation K) := by
  apply Polynomial.ringHom_ext
  · intro p; simp [RingHom.comp_apply]
  · simp [RingHom.comp_apply, presentation_root_sq]

theorem source_comp_presentationToSource :
    (sourceToPresentation K).comp (presentationToSource K) = RingHom.id _ := by
  apply AdjoinRoot.ringHom_ext
  · simp only [RingHom.comp_assoc, presentationToSource, AdjoinRoot.lift_comp_of,
      RingHom.id_comp]
    exact sourceToPresentation_comp_square K
  · simp [RingHom.comp_apply, presentationToSource]

def squarePresentationEquiv : AdjoinRoot (squareRelation K) ≃+* Polynomial K :=
  RingEquiv.ofRingHom (presentationToSource K) (sourceToPresentation K)
    (presentationToSource_comp_source K) (source_comp_presentationToSource K)

/-- A separate type for the source ring prevents the nonidentity target action
from being confused with the ring's usual self-action. -/
def SquareSourceRing := Polynomial K
instance : CommRing (SquareSourceRing K) := inferInstanceAs (CommRing (Polynomial K))
instance squareSourceAlgebra : Algebra (Polynomial K) (SquareSourceRing K) :=
  (show Polynomial K →+* SquareSourceRing K from squarePullback K).toAlgebra

/-- The presentation respects the actual square pullback algebra. -/
def squarePresentationAlgEquiv :
    AdjoinRoot (squareRelation K) ≃ₐ[Polynomial K] SquareSourceRing K :=
  { squarePresentationEquiv K with commutes' := fun _ => AdjoinRoot.lift_of _ }

/-- The actual residue-field tensor product has the expected quadratic presentation. -/
def squareFiberEquiv (p : PrimeSpectrum (Polynomial K)) :
    p.asIdeal.Fiber (SquareSourceRing K) ≃+*
      AdjoinRoot (X ^ 2 - C (algebraMap (Polynomial K) p.asIdeal.ResidueField X)) := by
  let e₁ := Algebra.TensorProduct.congr
    (AlgEquiv.refl : p.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField] p.asIdeal.ResidueField)
    (squarePresentationAlgEquiv K).symm
  let q := (squareRelation K).map
    (Algebra.TensorProduct.includeRight : Polynomial K →ₐ[Polynomial K]
      p.asIdeal.ResidueField ⊗[Polynomial K] Polynomial K).toRingHom
  let e₂ := AdjoinRoot.tensorAlgEquiv (R := Polynomial K) (T := p.asIdeal.ResidueField)
    (squareRelation K) q rfl
  let e₃ := AdjoinRoot.mapAlgEquiv
    (Algebra.TensorProduct.rid (Polynomial K) p.asIdeal.ResidueField p.asIdeal.ResidueField)
    q (X ^ 2 - C (algebraMap (Polynomial K) p.asIdeal.ResidueField X))
    (Associated.of_eq (by simp [q, squareRelation, Algebra.smul_def]))
  exact e₁.toRingEquiv.trans (e₂.toRingEquiv.trans e₃.toRingEquiv)

set_option backward.isDefEq.respectTransparency false in
/-- Reducedness comparison for the actual affine-scheme fiber. -/
theorem square_fiber_isReduced_iff_ring (p : PrimeSpectrum (Polynomial K)) :
    IsReduced ((squareMap K).fiber p) ↔
      _root_.IsReduced (p.asIdeal.Fiber (SquareSourceRing K)) := by
  let e := Spec.fiberToSpecResidueFieldIso (Polynomial K) (SquareSourceRing K) p
  constructor
  · intro h
    exact (affine_isReduced_iff _).mp
      (@isReduced_of_isOpenImmersion _ _ e.inv.left inferInstance h)
  · intro h
    let : IsIso e.hom.left := (Arrow.leftFunc.mapIso e).isIso_hom
    have hspec := (affine_isReduced_iff (.of (p.asIdeal.Fiber (SquareSourceRing K)))).mpr h
    exact @isReduced_of_isOpenImmersion _ _ e.hom.left (IsOpenImmersion.of_isIso _) hspec

/-- The actual squaring map has a nonreduced fiber precisely over `x=0`. -/
theorem square_fiber_isReduced_iff [CharZero K] (p : PrimeSpectrum (Polynomial K)) :
    IsReduced ((squareMap K).fiber p) ↔ (X : Polynomial K) ∉ p.asIdeal := by
  rw [square_fiber_isReduced_iff_ring]
  let : Algebra K p.asIdeal.ResidueField :=
    ((algebraMap (Polynomial K) p.asIdeal.ResidueField).comp
      (algebraMap K (Polynomial K))).toAlgebra
  let : CharZero p.asIdeal.ResidueField := Algebra.charZero_of_charZero K _
  have he : _root_.IsReduced (p.asIdeal.Fiber (SquareSourceRing K)) ↔
      _root_.IsReduced
        (AdjoinRoot (X ^ 2 - C (algebraMap (Polynomial K) p.asIdeal.ResidueField X))) := by
    constructor
    · intro h
      let : _root_.IsReduced (p.asIdeal.Fiber (SquareSourceRing K)) := h
      exact isReduced_of_injective (squareFiberEquiv K p).symm
        (squareFiberEquiv K p).symm.injective
    · intro h
      let : _root_.IsReduced
          (AdjoinRoot (X ^ 2 - C (algebraMap (Polynomial K) p.asIdeal.ResidueField X))) := h
      exact isReduced_of_injective (squareFiberEquiv K p) (squareFiberEquiv K p).injective
  rw [he, CharZeroPaperSmoothBranch.quadratic_isReduced_iff, ne_eq,
    Ideal.algebraMap_residueField_eq_zero]

def axisIdeal : Ideal (Polynomial K) := Ideal.span {X}

instance axisIdeal_isPrime : (axisIdeal K).IsPrime :=
  (Ideal.span_singleton_prime X_ne_zero).mpr prime_X

theorem axisIdeal_height : (axisIdeal K).height = 1 :=
  Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr X_ne_zero) (not_isUnit_X : ¬ IsUnit (X : Polynomial K))

def axisDivisorPoint : SchemeDivisorPoint (line K) :=
  ⟨⟨axisIdeal K, inferInstance⟩,
    (idealHeight_eq_coheight (.of (Polynomial K)) ⟨axisIdeal K, inferInstance⟩).symm.trans
      (axisIdeal_height K)⟩

set_option backward.isDefEq.respectTransparency false in
/-- The sole actual codimension-one nonreduced-fiber divisor is `x=0`. -/
theorem square_reducedFiberBranch [CharZero K] :
    schemeReducedFiberBranch (squareMap K) = {axisDivisorPoint K} := by
  ext Q
  change (¬ IsReduced ((squareMap K).fiber Q.1)) ↔ Q = axisDivisorPoint K
  rw [square_fiber_isReduced_iff, not_not]
  constructor
  · intro hx
    have hheight : Q.1.asIdeal.height = 1 :=
      (idealHeight_eq_coheight (.of (Polynomial K)) Q.1).trans Q.2
    let : (axisIdeal K).FiniteHeight := by
      simp [Ideal.finiteHeight_iff, axisIdeal_height]
    have he : axisIdeal K = Q.1.asIdeal := Ideal.eq_of_le_of_height_le (axisIdeal K)
      (Ideal.span_le.mpr (by simpa using hx)) (by rw [hheight, axisIdeal_height])
    apply Subtype.ext
    exact PrimeSpectrum.ext he.symm
  · rintro rfl
    exact Ideal.subset_span (Set.mem_singleton _)

set_option backward.isDefEq.respectTransparency false in
/-- Actual codimension-one branch support is exactly the coordinate axis. -/
theorem square_reducedFiberBranch_support [CharZero K] :
    divisorSupport (schemeReducedFiberBranch (squareMap K)) =
      {p : line K | (X : Polynomial K) ∈ p.asIdeal} := by
  rw [square_reducedFiberBranch]
  simp only [divisorSupport, Set.biUnion_singleton]
  change closure ({⟨axisIdeal K, inferInstance⟩} : Set (PrimeSpectrum (Polynomial K))) = _
  rw [PrimeSpectrum.closure_singleton]
  ext p
  change axisIdeal K ≤ p.asIdeal ↔ (X : Polynomial K) ∈ p.asIdeal
  simp [axisIdeal, Ideal.span_le]


instance line_isIntegral : IsIntegral (line K) := inferInstance
instance line_isNormal : IsNormalScheme (line K) :=
  CharZeroPaperSmoothBranch.normal_spec (Polynomial K)

/-- The actual normalized branch of the restricted line map is its origin. -/
theorem normalized_square_branch [CharZero K] :
    normalizedMorphismBranchSupport (squareMap K) =
      {p : line K | (X : Polynomial K) ∈ p.asIdeal} := by
  rw [CharZeroPaperSmoothBranch.normalized_support_eq_reduced_support,
    square_reducedFiberBranch_support]

instance axisIdeal_isMaximal : (axisIdeal K).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (Polynomial.irreducible_X (R := K))

/-- In the restricted target line, the branch support is precisely the closed origin. -/
theorem normalized_square_branch_singleton [CharZero K] :
    normalizedMorphismBranchSupport (squareMap K) = {(axisDivisorPoint K).1} := by
  rw [normalized_square_branch]
  ext p
  change (X : Polynomial K) ∈ p.asIdeal ↔ p = (axisDivisorPoint K).1
  constructor
  · intro hx
    have he : axisIdeal K = p.asIdeal :=
      (axisIdeal_isMaximal K).eq_of_le p.isPrime.ne_top
        (Ideal.span_le.mpr (by simpa using hx))
    exact PrimeSpectrum.ext he.symm
  · rintro rfl
    exact Ideal.subset_span (Set.mem_singleton _)

/-- The cone vertex, obtained from the origin of its actual closed target line. -/
def vertex : cone K := targetLine K (axisDivisorPoint K).1

/-- All three displayed coordinates vanish at this scheme point. -/
theorem vertex_coordinates (i : Fin 3) :
    Ideal.Quotient.mk (Cusp.coneIdeal K) (MvPolynomial.X i) ∈ (vertex K).asIdeal := by
  change targetLinePullback K (Ideal.Quotient.mk _ (MvPolynomial.X i)) ∈ axisIdeal K
  change (MvPolynomial.aeval ![(X : Polynomial K), 0, 0]) (MvPolynomial.X i) ∈ axisIdeal K
  fin_cases i
  · simp only [MvPolynomial.aeval_X]
    exact Ideal.subset_span (Set.mem_singleton _)
  · simp
  · simp

/-- The normalized branch of the restricted line is carried to exactly the cone vertex. -/
theorem restricted_branch_image [CharZero K] :
    targetLine K '' normalizedMorphismBranchSupport (squareMap K) = {vertex K} := by
  rw [normalized_square_branch_singleton]
  exact Set.image_singleton

/-- The x and z coordinates give the even part of the cone coordinate ring. -/
def evenCoordinates : MvPolynomial (Fin 2) K →ₐ[K] ConeRing K :=
  MvPolynomial.aeval ![Ideal.Quotient.mk _ (MvPolynomial.X 0),
    Ideal.Quotient.mk _ (MvPolynomial.X 2)]

abbrev middleCoordinate : ConeRing K := Ideal.Quotient.mk _ (MvPolynomial.X 1)

theorem middleCoordinate_sq :
    middleCoordinate K ^ 2 = evenCoordinates K (MvPolynomial.X 0 * MvPolynomial.X 1) := by
  have h : Ideal.Quotient.mk (Cusp.coneIdeal K)
      (MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 1 ^ 2) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have he := sub_eq_zero.mp (show
      Ideal.Quotient.mk (Cusp.coneIdeal K) (MvPolynomial.X 0) *
        Ideal.Quotient.mk _ (MvPolynomial.X 2) - middleCoordinate K ^ 2 = 0 by
    simpa only [map_sub, map_mul, map_pow] using h)
  simpa [evenCoordinates] using he.symm

/-- Every class has the normal form `a(x,z)+y b(x,z)`. -/
theorem cone_normalForm (q : ConeRing K) :
    ∃ a b : MvPolynomial (Fin 2) K,
      q = evenCoordinates K a + middleCoordinate K * evenCoordinates K b := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  induction p using MvPolynomial.induction_on with
  | C c =>
    refine ⟨MvPolynomial.C c, 0, ?_⟩
    simp [evenCoordinates]
    rfl
  | add p q hp hq =>
    obtain ⟨a,b,ha⟩ := hp
    obtain ⟨c,d,hb⟩ := hq
    refine ⟨a+c,b+d,?_⟩
    rw [map_add, ha, hb]
    simp only [map_add]
    ring
  | mul_X p i hp =>
    obtain ⟨a,b,ha⟩ := hp
    fin_cases i
    · refine ⟨a * MvPolynomial.X 0, b * MvPolynomial.X 0, ?_⟩
      rw [map_mul, ha]
      simp only [map_mul]
      have hx : evenCoordinates K (MvPolynomial.X 0) =
          Ideal.Quotient.mk _ (MvPolynomial.X 0) := by simp [evenCoordinates]
      rw [hx]
      ring_nf
      rfl
    · refine ⟨b * (MvPolynomial.X 0 * MvPolynomial.X 1), a, ?_⟩
      rw [map_mul, ha]
      change (_ + middleCoordinate K * _) * middleCoordinate K = _
      rw [map_mul, ← middleCoordinate_sq]
      ring
    · refine ⟨a * MvPolynomial.X 1, b * MvPolynomial.X 1, ?_⟩
      rw [map_mul, ha]
      simp only [map_mul]
      have hx : evenCoordinates K (MvPolynomial.X 1) =
          Ideal.Quotient.mk _ (MvPolynomial.X 2) := by simp [evenCoordinates]
      rw [hx]
      ring_nf
      rfl

theorem coneParam_evenCoordinates (a : MvPolynomial (Fin 2) K) :
    Cusp.coneParam K (evenCoordinates K a) = MvPolynomial.expand 2 a := by
  have h : (Cusp.coneParam K).comp (evenCoordinates K) = MvPolynomial.expand 2 := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, evenCoordinates, MvPolynomial.aeval_X,
      MvPolynomial.expand_X]
    fin_cases i
    · change (MvPolynomial.aeval (Cusp.coneMap K)) (MvPolynomial.X 0) =
        (MvPolynomial.X 0 : SourceRing K) ^ 2
      simp [Cusp.coneMap]
    · change (MvPolynomial.aeval (Cusp.coneMap K)) (MvPolynomial.X 2) =
        (MvPolynomial.X 1 : SourceRing K) ^ 2
      simp [Cusp.coneMap]
  exact congrArg (fun f : MvPolynomial (Fin 2) K →ₐ[K] SourceRing K => f a) h

theorem coneParam_middleCoordinate :
    Cusp.coneParam K (middleCoordinate K) = MvPolynomial.X 0 * MvPolynomial.X 1 := by
  change (MvPolynomial.aeval (Cusp.coneMap K)) (MvPolynomial.X 1) = _
  simp [Cusp.coneMap]

/-- Changing the sign of u separates the even and odd normal-form summands. -/
def signChange : SourceRing K →ₐ[K] SourceRing K :=
  MvPolynomial.aeval ![-MvPolynomial.X 0, MvPolynomial.X 1]

theorem signChange_expand (a : SourceRing K) :
    signChange K (MvPolynomial.expand 2 a) = MvPolynomial.expand 2 a := by
  have h : (signChange K).comp (MvPolynomial.expand 2) = MvPolynomial.expand 2 := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [signChange]
  exact congrArg (fun f : SourceRing K →ₐ[K] SourceRing K => f a) h

/-- The displayed cone quotient embeds in k[u,v]; no domain property of the quotient is assumed. -/
theorem coneParam_injective [CharZero K] : Function.Injective (Cusp.coneParam K) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro q hq
  obtain ⟨a,b,rfl⟩ := cone_normalForm K q
  rw [map_add, map_mul, coneParam_evenCoordinates, coneParam_evenCoordinates,
    coneParam_middleCoordinate] at hq
  have hs := congrArg (signChange K) hq
  simp only [map_add, map_mul, map_zero, signChange_expand] at hs
  have hu : signChange K (MvPolynomial.X 0) = -MvPolynomial.X 0 := by simp [signChange]
  have hv : signChange K (MvPolynomial.X 1) = MvPolynomial.X 1 := by simp [signChange]
  rw [hu,hv] at hs
  have ha : MvPolynomial.expand 2 a = 0 := by
    have ht : (2 : SourceRing K) * MvPolynomial.expand 2 a = 0 := by
      linear_combination hq + hs
    exact (mul_eq_zero.mp ht).resolve_left (by norm_num)
  have hb : MvPolynomial.expand 2 b = 0 := by
    rw [ha, zero_add] at hq
    exact (mul_eq_zero.mp hq).resolve_left
      (mul_ne_zero (MvPolynomial.X_ne_zero 0) (MvPolynomial.X_ne_zero 1))
  have ha' : a = 0 := (MvPolynomial.expand_eq_zero (by decide : 0 < 2)).mp ha
  have hb' : b = 0 := (MvPolynomial.expand_eq_zero (by decide : 0 < 2)).mp hb
  simp [ha',hb']

/-- The sole algebraic relation among u², uv, v² is the displayed cone equation. -/
theorem coneIdeal_eq_ker [CharZero K] :
    Cusp.coneIdeal K = RingHom.ker (MvPolynomial.aeval (Cusp.coneMap K)).toRingHom := by
  ext p
  rw [RingHom.mem_ker]
  constructor
  · intro hp
    change Cusp.coneParam K (Ideal.Quotient.mk (Cusp.coneIdeal K) p) = 0
    have h := congrArg (Cusp.coneParam K) (Ideal.Quotient.eq_zero_iff_mem.mpr hp)
    simpa only [map_zero] using h
  · intro hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply coneParam_injective K
    change (MvPolynomial.aeval (Cusp.coneMap K)) p = 0
    exact hp

instance coneRing_isDomain [CharZero K] : IsDomain (ConeRing K) :=
  Function.Injective.isDomain (Cusp.coneParam K).toRingHom (coneParam_injective K)

instance cone_isIntegral [CharZero K] : IsIntegral (cone K) := inferInstance

/-- The actual finite cone map is surjective, by lying over for its injective ring map. -/
instance coneMap_surjective [CharZero K] : Surjective (coneMap K) := by
  constructor
  exact (coneParam_finite K).to_isIntegral.comap_surjective (coneParam_injective K)

end Pcf.Examples.CharZeroPaperConeBranch

#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneParam_finite
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneMap_finite
#print axioms Pcf.Examples.CharZeroPaperConeBranch.targetLinePullback_surjective
#print axioms Pcf.Examples.CharZeroPaperConeBranch.targetLine_closedImmersion
#print axioms Pcf.Examples.CharZeroPaperConeBranch.sourceLinePullback_surjective
#print axioms Pcf.Examples.CharZeroPaperConeBranch.sourceLine_closedImmersion
#print axioms Pcf.Examples.CharZeroPaperConeBranch.restriction_square
#print axioms Pcf.Examples.CharZeroPaperConeBranch.squarePullback_X
#print axioms Pcf.Examples.CharZeroPaperConeBranch.squarePullback_C
#print axioms Pcf.Examples.CharZeroPaperConeBranch.squarePullback_finite
#print axioms Pcf.Examples.CharZeroPaperConeBranch.squareMap_finite
#print axioms Pcf.Examples.CharZeroPaperConeBranch.squareMap_surjective
#print axioms Pcf.Examples.CharZeroPaperConeBranch.sourceToPresentation_C
#print axioms Pcf.Examples.CharZeroPaperConeBranch.sourceToPresentation_X
#print axioms Pcf.Examples.CharZeroPaperConeBranch.presentation_root_sq
#print axioms Pcf.Examples.CharZeroPaperConeBranch.presentationToSource_comp_source
#print axioms Pcf.Examples.CharZeroPaperConeBranch.sourceToPresentation_comp_square
#print axioms Pcf.Examples.CharZeroPaperConeBranch.source_comp_presentationToSource
#print axioms Pcf.Examples.CharZeroPaperConeBranch.squarePresentationEquiv
#print axioms Pcf.Examples.CharZeroPaperConeBranch.squareSourceAlgebra
#print axioms Pcf.Examples.CharZeroPaperConeBranch.squarePresentationAlgEquiv
#print axioms Pcf.Examples.CharZeroPaperConeBranch.squareFiberEquiv
#print axioms Pcf.Examples.CharZeroPaperConeBranch.square_fiber_isReduced_iff_ring
#print axioms Pcf.Examples.CharZeroPaperConeBranch.square_fiber_isReduced_iff
#print axioms Pcf.Examples.CharZeroPaperConeBranch.axisIdeal_isPrime
#print axioms Pcf.Examples.CharZeroPaperConeBranch.axisIdeal_height
#print axioms Pcf.Examples.CharZeroPaperConeBranch.square_reducedFiberBranch
#print axioms Pcf.Examples.CharZeroPaperConeBranch.square_reducedFiberBranch_support
#print axioms Pcf.Examples.CharZeroPaperConeBranch.line_isIntegral
#print axioms Pcf.Examples.CharZeroPaperConeBranch.line_isNormal
#print axioms Pcf.Examples.CharZeroPaperConeBranch.normalized_square_branch
#print axioms Pcf.Examples.CharZeroPaperConeBranch.axisIdeal_isMaximal
#print axioms Pcf.Examples.CharZeroPaperConeBranch.normalized_square_branch_singleton
#print axioms Pcf.Examples.CharZeroPaperConeBranch.vertex_coordinates
#print axioms Pcf.Examples.CharZeroPaperConeBranch.restricted_branch_image
#print axioms Pcf.Examples.CharZeroPaperConeBranch.middleCoordinate_sq
#print axioms Pcf.Examples.CharZeroPaperConeBranch.cone_normalForm
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneParam_evenCoordinates
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneParam_middleCoordinate
#print axioms Pcf.Examples.CharZeroPaperConeBranch.signChange_expand
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneParam_injective
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneIdeal_eq_ker
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneRing_isDomain
#print axioms Pcf.Examples.CharZeroPaperConeBranch.cone_isIntegral
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneMap_surjective
