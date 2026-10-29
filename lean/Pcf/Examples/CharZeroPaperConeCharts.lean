/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.CharZeroPaperConeBranch
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Coordinates, invariants, vertex, lines and chart localizations of the cone

Supporting material for `ex:branch-singular` on the actual cone scheme of
`CharZeroPaperConeBranch`:

* the cone coordinates `x, y, z` and the relation `y² = xz`;
* the sign change `(u,v) ↦ (-u,-v)`, whose fixed polynomials are exactly the
  image of the cone ring (`negBoth_fixed_iff`), and the integral closedness of
  the cone ring deduced from it (`cone_isIntegrallyClosed`);
* the vertex locus `V(x,y,z) = {vertex}` and the fibre of `coneMap` over the vertex;
* the source and target lines `V(v)` and `V(y,z)` as exact zero loci;
* the punctured cone `D(x) ∪ D(z)`, the chart localizations over `D(x)` and `D(z)`,
  and their identification with the restrictions of `coneMap`;
* the standard étale pair of a quadratic polynomial `T² - a` with `a` and `2` units.
-/

@[expose] public section
noncomputable section
namespace Pcf.Examples.CharZeroPaperConeBranch
open CategoryTheory AlgebraicGeometry Polynomial
universe u
variable (K : Type u) [Field K]

set_option backward.isDefEq.respectTransparency false

/-! ### Cone coordinates -/

/-- The cone coordinate `x`. -/
def coneX : ConeRing K := Ideal.Quotient.mk _ (MvPolynomial.X 0)
/-- The cone coordinate `y`. -/
def coneY : ConeRing K := Ideal.Quotient.mk _ (MvPolynomial.X 1)
/-- The cone coordinate `z`. -/
def coneZ : ConeRing K := Ideal.Quotient.mk _ (MvPolynomial.X 2)

theorem coneY_sq : coneY K ^ 2 = coneX K * coneZ K := by
  have hrel : Ideal.Quotient.mk (Cusp.coneIdeal K)
      (MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 1 ^ 2) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  simp only [map_sub, map_mul, map_pow, sub_eq_zero] at hrel
  exact hrel.symm

@[simp] theorem coneParam_x : Cusp.coneParam K (coneX K) = MvPolynomial.X 0 ^ 2 := by
  change MvPolynomial.aeval (Cusp.coneMap K) (MvPolynomial.X 0) = _
  simp [Cusp.coneMap]

@[simp] theorem coneParam_y :
    Cusp.coneParam K (coneY K) = MvPolynomial.X 0 * MvPolynomial.X 1 := by
  change MvPolynomial.aeval (Cusp.coneMap K) (MvPolynomial.X 1) = _
  simp [Cusp.coneMap]

@[simp] theorem coneParam_z : Cusp.coneParam K (coneZ K) = MvPolynomial.X 1 ^ 2 := by
  change MvPolynomial.aeval (Cusp.coneMap K) (MvPolynomial.X 2) = _
  simp [Cusp.coneMap]

/-! ### The sign change and the invariant ring -/

/-- The involution `(u,v) ↦ (-u,-v)` of the plane. -/
def negBoth : SourceRing K →ₐ[K] SourceRing K :=
  MvPolynomial.aeval ![-MvPolynomial.X 0, -MvPolynomial.X 1]

@[simp] theorem negBoth_X0 : negBoth K (MvPolynomial.X 0) = -MvPolynomial.X 0 := by
  simp [negBoth]

@[simp] theorem negBoth_X1 : negBoth K (MvPolynomial.X 1) = -MvPolynomial.X 1 := by
  simp [negBoth]

theorem negBoth_expand (a : MvPolynomial (Fin 2) K) :
    negBoth K (MvPolynomial.expand 2 a) = MvPolynomial.expand 2 a := by
  have h : (negBoth K).comp (MvPolynomial.expand 2) =
      (MvPolynomial.expand 2 : MvPolynomial (Fin 2) K →ₐ[K] SourceRing K) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [negBoth]
  exact congrArg (fun f : MvPolynomial (Fin 2) K →ₐ[K] SourceRing K => f a) h

/-- Cone functions are fixed by the sign change. -/
theorem negBoth_coneParam (q : ConeRing K) :
    negBoth K (Cusp.coneParam K q) = Cusp.coneParam K q := by
  obtain ⟨a, b, rfl⟩ := cone_normalForm K q
  rw [map_add, map_mul, coneParam_evenCoordinates, coneParam_evenCoordinates,
    coneParam_middleCoordinate, map_add, map_mul, negBoth_expand, negBoth_expand, map_mul,
    negBoth_X0, negBoth_X1, neg_mul_neg]

/-- The plane ring is generated as a module over the cone by `1, u, v`. -/
theorem plane_decomposition (p : SourceRing K) :
    ∃ a b c : ConeRing K,
      p = Cusp.coneParam K a + MvPolynomial.X 0 * Cusp.coneParam K b +
        MvPolynomial.X 1 * Cusp.coneParam K c := by
  induction p using MvPolynomial.induction_on with
  | C t =>
      refine ⟨algebraMap K _ t, 0, 0, ?_⟩
      simp only [map_zero, mul_zero, add_zero, AlgHom.commutes]
      rfl
  | add p q hp hq =>
      obtain ⟨a, b, c, rfl⟩ := hp
      obtain ⟨a', b', c', rfl⟩ := hq
      refine ⟨a + a', b + b', c + c', ?_⟩
      simp only [map_add]
      ring
  | mul_X p i hp =>
      obtain ⟨a, b, c, rfl⟩ := hp
      fin_cases i
      · refine ⟨coneX K * b + coneY K * c, a, 0, ?_⟩
        simp only [map_add, map_mul, map_zero, mul_zero, add_zero, coneParam_x, coneParam_y]
        change _ * MvPolynomial.X 0 = _
        ring
      · refine ⟨coneY K * b + coneZ K * c, 0, a, ?_⟩
        simp only [map_add, map_mul, map_zero, mul_zero, add_zero, coneParam_y, coneParam_z]
        change _ * MvPolynomial.X 1 = _
        ring

/-- Polynomials fixed by `(u,v) ↦ (-u,-v)` are precisely the cone functions. -/
theorem negBoth_fixed_iff [CharZero K] (p : SourceRing K) :
    negBoth K p = p ↔ ∃ a, Cusp.coneParam K a = p := by
  constructor
  · intro hp
    obtain ⟨a, b, c, h⟩ := plane_decomposition K p
    refine ⟨a, ?_⟩
    have hneg := congrArg (negBoth K) h
    simp only [map_add, map_mul, negBoth_coneParam, negBoth_X0, negBoth_X1] at hneg
    rw [hp] at hneg
    have h2 : (2 : SourceRing K) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h2
    linear_combination -h - hneg
  · rintro ⟨a, rfl⟩
    exact negBoth_coneParam K a

/-- The cone coordinate ring is integrally closed: it is the invariant ring of the
integrally closed polynomial ring under the sign change. -/
theorem cone_isIntegrallyClosed [CharZero K] : IsIntegrallyClosed (ConeRing K) := by
  let R := ConeRing K
  let S := SourceRing K
  let : Algebra R S := (Cusp.coneParam K).toRingHom.toAlgebra
  have : FaithfulSMul R S :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (coneParam_injective K)
  let KR := FractionRing R
  let L := FractionRing S
  let : Algebra KR L := FractionRing.liftAlgebra R L
  have : IsScalarTower R KR L := FractionRing.isScalarTower_liftAlgebra R L
  apply (isIntegrallyClosed_iff KR).mpr
  intro x hx
  have hxL : IsIntegral R (algebraMap KR L x) :=
    hx.map (IsScalarTower.toAlgHom R KR L)
  have hxS : IsIntegral S (algebraMap KR L x) := hxL.tower_top
  obtain ⟨p, hp⟩ := (isIntegrallyClosed_iff L).mp (inferInstance : IsIntegrallyClosed S) hxS
  obtain ⟨a, b, hb, hxfrac⟩ := IsFractionRing.div_surjective R x
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hab : p * algebraMap R S b = algebraMap R S a := by
    apply IsFractionRing.injective S L
    rw [map_mul, ← IsScalarTower.algebraMap_apply R S L,
      ← IsScalarTower.algebraMap_apply R S L, hp, IsScalarTower.algebraMap_apply R KR L,
      IsScalarTower.algebraMap_apply R KR L, ← map_mul]
    congr 1
    rw [← hxfrac]
    exact div_mul_cancel₀ _ (by simpa only [map_zero] using (IsFractionRing.injective R KR).ne hb0)
  have hbS : algebraMap R S b ≠ 0 := (FaithfulSMul.algebraMap_injective R S).ne hb0
  have hfix : negBoth K p = p := by
    apply mul_right_cancel₀ hbS
    have hneg := congrArg (negBoth K) hab
    rw [map_mul] at hneg
    change negBoth K p * negBoth K (Cusp.coneParam K b) =
      negBoth K (Cusp.coneParam K a) at hneg
    rw [negBoth_coneParam, negBoth_coneParam] at hneg
    exact hneg.trans hab.symm
  obtain ⟨c, hc⟩ := (negBoth_fixed_iff K p).mp hfix
  refine ⟨c, ?_⟩
  apply (algebraMap KR L).injective
  have hc' : algebraMap R S c = p := hc
  rw [← IsScalarTower.algebraMap_apply R KR L,
    IsScalarTower.algebraMap_apply R S L, hc', hp]

/-! ### The vertex locus and the fibre over the vertex -/

/-- A polynomial differs from its constant term by an element of any ideal
containing the images of all variables. -/
theorem sub_constantCoeff_mem {σ : Type*} {A : Type*} [CommRing A] [Algebra K A]
    (φ : MvPolynomial σ K →ₐ[K] A) (I : Ideal A) (hX : ∀ i, φ (MvPolynomial.X i) ∈ I)
    (P : MvPolynomial σ K) :
    φ P - algebraMap K A (MvPolynomial.constantCoeff P) ∈ I := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    convert I.add_mem hp hq using 1
    simp only [map_add]
    ring
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.constantCoeff_X, mul_zero, map_zero, sub_zero]
    exact I.mul_mem_left _ (hX i)

/-- Evaluation at the vertex, read through the target line. -/
def vertexEval : ConeRing K →ₐ[K] K := (Polynomial.aeval (0 : K)).comp (targetLinePullback K)

theorem vertexEval_mk (P : MvPolynomial (Fin 3) K) :
    vertexEval K (Ideal.Quotient.mk _ P) = MvPolynomial.constantCoeff P := by
  have h : (vertexEval K).toRingHom.comp (Ideal.Quotient.mk (Cusp.coneIdeal K)) =
      MvPolynomial.constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [vertexEval, targetLinePullback]
    · intro i
      fin_cases i <;> simp [vertexEval, targetLinePullback]
  exact congrArg (fun g : MvPolynomial (Fin 3) K →+* K => g P) h

theorem mem_vertex_iff (r : ConeRing K) : r ∈ (vertex K).asIdeal ↔ vertexEval K r = 0 := by
  change targetLinePullback K r ∈ axisIdeal K ↔ _
  rw [axisIdeal, Ideal.mem_span_singleton, Polynomial.X_dvd_iff,
    Polynomial.coeff_zero_eq_eval_zero]
  rfl

theorem vertex_eq_ker : (vertex K).asIdeal = RingHom.ker (vertexEval K) := by
  ext r
  rw [mem_vertex_iff, RingHom.mem_ker]

instance vertex_isMaximal : (vertex K).asIdeal.IsMaximal := by
  rw [vertex_eq_ker]
  exact RingHom.ker_isMaximal_of_surjective _ fun a => ⟨algebraMap K _ a, by simp⟩

/-- The closed locus `V(x,y,z)` of the cone. -/
def vertexLocus : Set (cone K) :=
  {p | coneX K ∈ p.asIdeal ∧ coneY K ∈ p.asIdeal ∧ coneZ K ∈ p.asIdeal}

/-- `V(x,y,z)` is the single vertex point. -/
theorem mem_vertexLocus_iff (p : cone K) : p ∈ vertexLocus K ↔ p = vertex K := by
  constructor
  · rintro ⟨hx, hy, hz⟩
    have hle : (vertex K).asIdeal ≤ p.asIdeal := by
      intro r hr
      obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective r
      have hsub := sub_constantCoeff_mem K (Ideal.Quotient.mkₐ K (Cusp.coneIdeal K))
        p.asIdeal (by
          intro i
          fin_cases i
          · exact hx
          · exact hy
          · exact hz) P
      rw [mem_vertex_iff, vertexEval_mk] at hr
      rw [hr, map_zero, sub_zero] at hsub
      exact hsub
    exact (PrimeSpectrum.ext ((vertex_isMaximal K).eq_of_le p.isPrime.ne_top hle)).symm
  · rintro rfl
    exact ⟨vertex_coordinates K 0, vertex_coordinates K 1, vertex_coordinates K 2⟩

/-- The closed origin of the source plane. -/
def planeOrigin : sourcePlane K :=
  ⟨RingHom.ker (MvPolynomial.constantCoeff : SourceRing K →+* K), RingHom.ker_isPrime _⟩

instance planeOrigin_isMaximal : (planeOrigin K).asIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun a => ⟨MvPolynomial.C a, by simp⟩

/-- A plane prime contains both coordinates exactly when it is the origin. -/
theorem coordinates_mem_iff_planeOrigin (q : sourcePlane K) :
    (MvPolynomial.X 0 ∈ q.asIdeal ∧ MvPolynomial.X 1 ∈ q.asIdeal) ↔ q = planeOrigin K := by
  constructor
  · rintro ⟨hu, hv⟩
    have hle : (planeOrigin K).asIdeal ≤ q.asIdeal := by
      intro P hP
      have hsub := sub_constantCoeff_mem K (AlgHom.id K (SourceRing K)) q.asIdeal (by
        intro i
        fin_cases i
        · exact hu
        · exact hv) P
      have hP' : MvPolynomial.constantCoeff P = 0 := hP
      rw [hP', map_zero, sub_zero] at hsub
      exact hsub
    exact (PrimeSpectrum.ext ((planeOrigin_isMaximal K).eq_of_le q.isPrime.ne_top hle)).symm
  · rintro rfl
    exact ⟨MvPolynomial.constantCoeff_X _ _, MvPolynomial.constantCoeff_X _ _⟩

/-- The origin is the unique source point mapping to the vertex. -/
theorem coneMap_eq_vertex_iff (q : sourcePlane K) : coneMap K q = vertex K ↔ q = planeOrigin K := by
  rw [← mem_vertexLocus_iff, ← coordinates_mem_iff_planeOrigin]
  constructor
  · rintro ⟨hx, -, hz⟩
    change Cusp.coneParam K (coneX K) ∈ q.asIdeal at hx
    change Cusp.coneParam K (coneZ K) ∈ q.asIdeal at hz
    rw [coneParam_x] at hx
    rw [coneParam_z] at hz
    exact ⟨q.isPrime.mem_of_pow_mem 2 hx, q.isPrime.mem_of_pow_mem 2 hz⟩
  · rintro ⟨hu, hv⟩
    refine ⟨?_, ?_, ?_⟩
    · change Cusp.coneParam K (coneX K) ∈ q.asIdeal
      rw [coneParam_x, pow_two]; exact q.asIdeal.mul_mem_left _ hu
    · change Cusp.coneParam K (coneY K) ∈ q.asIdeal
      rw [coneParam_y]; exact q.asIdeal.mul_mem_left _ hv
    · change Cusp.coneParam K (coneZ K) ∈ q.asIdeal
      rw [coneParam_z, pow_two]; exact q.asIdeal.mul_mem_left _ hv

/-- The origin of the plane is the only point over the vertex. -/
theorem coneMap_preimage_vertex : coneMap K ⁻¹' {vertex K} = {planeOrigin K} := by
  ext q
  exact coneMap_eq_vertex_iff K q

/-- A height-one prime of the plane cannot contain both coordinates. -/
theorem plane_heightOne_not_both_coordinates (p : PrimeSpectrum (SourceRing K))
    (hp : p.asIdeal.height = 1) :
    ¬ (MvPolynomial.X 0 ∈ p.asIdeal ∧ MvPolynomial.X 1 ∈ p.asIdeal) := by
  rintro ⟨hu, hv⟩
  have heq := Ideal.eq_span_singleton_of_height_eq_one hp hu
    (MvPolynomial.X_prime (R := K) (i := (0 : Fin 2)))
  rw [heq, Ideal.mem_span_singleton] at hv
  have hfalse : (0 : Fin 2) = 1 := MvPolynomial.X_dvd_X.mp hv
  exact (by decide : (0 : Fin 2) ≠ 1) hfalse

/-- No integral effective divisor of the plane maps to the vertex. -/
theorem coneMap_divisor_ne_vertex (Q : SchemeDivisorPoint (sourcePlane K)) :
    coneMap K Q.1 ≠ vertex K := by
  intro h
  rw [coneMap_eq_vertex_iff] at h
  apply plane_heightOne_not_both_coordinates K Q.1
    ((idealHeight_eq_coheight (.of (SourceRing K)) Q.1).trans Q.2)
  rw [h]
  exact (coordinates_mem_iff_planeOrigin K _).mpr rfl

/-! ### The two lines as zero loci -/

/-- The ideal `(v)` of the source line. -/
def sourceLineIdeal : Ideal (SourceRing K) := Ideal.span {MvPolynomial.X 1}

/-- The ideal `(y,z)` of the target line. -/
def targetLineIdeal : Ideal (ConeRing K) := Ideal.span {coneY K, coneZ K}

/-- `k[u,v]/(v) ≅ k[t]`. -/
def sourceLineQuotientEquiv : (SourceRing K ⧸ sourceLineIdeal K) ≃ₐ[K] Polynomial K := by
  refine AlgEquiv.ofAlgHom
    (Ideal.Quotient.liftₐ _ (sourceLinePullback K) (by
      intro p hp
      have hle : sourceLineIdeal K ≤ RingHom.ker (sourceLinePullback K).toRingHom := by
        rw [sourceLineIdeal, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
        simp [sourceLinePullback]
      exact hle hp))
    (Polynomial.aeval (Ideal.Quotient.mk _ (MvPolynomial.X 0))) ?_ ?_
  · apply Polynomial.algHom_ext
    simp [sourceLinePullback]
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [sourceLinePullback]
    · have hv : Ideal.Quotient.mk (sourceLineIdeal K) (MvPolynomial.X 1) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
      simpa [sourceLinePullback] using hv.symm

/-- `k[Y]/(y,z) ≅ k[t]`. -/
def targetLineQuotientEquiv : (ConeRing K ⧸ targetLineIdeal K) ≃ₐ[K] Polynomial K := by
  refine AlgEquiv.ofAlgHom
    (Ideal.Quotient.liftₐ _ (targetLinePullback K) (by
      intro p hp
      have hle : targetLineIdeal K ≤ RingHom.ker (targetLinePullback K).toRingHom := by
        rw [targetLineIdeal, Ideal.span_le]
        rintro q (rfl | rfl) <;>
          simp [RingHom.mem_ker, targetLinePullback, coneY, coneZ]
      exact hle hp))
    (Polynomial.aeval (Ideal.Quotient.mk _ (coneX K))) ?_ ?_
  · apply Polynomial.algHom_ext
    simp [targetLinePullback, coneX]
  · apply Ideal.Quotient.algHom_ext
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [targetLinePullback, coneX]
    · have hy : Ideal.Quotient.mk (targetLineIdeal K) (coneY K) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inl rfl))
      simpa [targetLinePullback, coneY] using hy.symm
    · have hz : Ideal.Quotient.mk (targetLineIdeal K) (coneZ K) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inr rfl))
      simpa [targetLinePullback, coneZ] using hz.symm

theorem sourceLinePullback_ker :
    RingHom.ker (sourceLinePullback K).toRingHom = sourceLineIdeal K := by
  ext p
  change sourceLinePullback K p = 0 ↔ p ∈ sourceLineIdeal K
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨fun hp => (sourceLineQuotientEquiv K).injective (by
    change sourceLinePullback K p = sourceLineQuotientEquiv K 0
    simpa using hp), fun hp => by
      have := congrArg (sourceLineQuotientEquiv K) hp
      simpa [sourceLineQuotientEquiv] using this⟩

theorem targetLinePullback_ker :
    RingHom.ker (targetLinePullback K).toRingHom = targetLineIdeal K := by
  ext p
  change targetLinePullback K p = 0 ↔ p ∈ targetLineIdeal K
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨fun hp => (targetLineQuotientEquiv K).injective (by
    change targetLinePullback K p = targetLineQuotientEquiv K 0
    simpa using hp), fun hp => by
      have := congrArg (targetLineQuotientEquiv K) hp
      simpa [targetLineQuotientEquiv] using this⟩

/-- The source line is `A = V(v)`. -/
theorem sourceLine_range :
    Set.range (sourceLine K) = PrimeSpectrum.zeroLocus {(MvPolynomial.X 1 : SourceRing K)} := by
  change Set.range (PrimeSpectrum.comap (sourceLinePullback K).toRingHom) = _
  rw [range_comap_of_surjective _ _ (sourceLinePullback_surjective K),
    sourceLinePullback_ker, sourceLineIdeal, PrimeSpectrum.zeroLocus_span]

/-- The target line is `B = V(y,z)`. -/
theorem targetLine_range :
    Set.range (targetLine K) = PrimeSpectrum.zeroLocus {coneY K, coneZ K} := by
  change Set.range (PrimeSpectrum.comap (targetLinePullback K).toRingHom) = _
  rw [range_comap_of_surjective _ _ (targetLinePullback_surjective K),
    targetLinePullback_ker, targetLineIdeal, PrimeSpectrum.zeroLocus_span]

instance targetLineIdeal_isPrime : (targetLineIdeal K).IsPrime := by
  rw [← targetLinePullback_ker]
  exact RingHom.ker_isPrime _

/-! ### The punctured cone -/

/-- The union `D(x) ∪ D(z)` of the two chart opens. -/
def puncturedOpen : (cone K).Opens :=
  PrimeSpectrum.basicOpen (coneX K) ⊔ PrimeSpectrum.basicOpen (coneZ K)

/-- The two chart opens cover exactly the complement of the vertex. -/
theorem mem_puncturedOpen_iff_ne_vertex (p : cone K) : p ∈ puncturedOpen K ↔ p ≠ vertex K := by
  rw [ne_eq, ← mem_vertexLocus_iff]
  change (coneX K ∉ p.asIdeal ∨ coneZ K ∉ p.asIdeal) ↔
    ¬(coneX K ∈ p.asIdeal ∧ coneY K ∈ p.asIdeal ∧ coneZ K ∈ p.asIdeal)
  constructor
  · rintro (hx | hz) ⟨hx', _, hz'⟩
    · exact hx hx'
    · exact hz hz'
  · intro h
    by_contra hnot
    simp only [not_or, not_not] at hnot
    obtain ⟨hx, hz⟩ := hnot
    have hy : coneY K ∈ p.asIdeal := by
      apply p.isPrime.mem_of_pow_mem 2
      rw [coneY_sq]
      exact mul_mem hx hz
    exact h ⟨hx, hy, hz⟩

/-- Off the vertex, a point lies in `D(x)` or `D(z)`. -/
theorem mem_basicOpen_x_or_z (p : cone K) (hp : p ≠ vertex K) :
    p ∈ PrimeSpectrum.basicOpen (coneX K) ∨ p ∈ PrimeSpectrum.basicOpen (coneZ K) :=
  (mem_puncturedOpen_iff_ne_vertex K p).mpr hp

/-! ### Chart localizations -/

/-- The target localization `k[Y]_x`. -/
abbrev TargetX := Localization.Away (coneX K)
/-- The source localization `k[u,v]_{u²}`. -/
abbrev SourceX := Localization.Away (Cusp.coneParam K (coneX K))
/-- The target localization `k[Y]_z`. -/
abbrev TargetZ := Localization.Away (coneZ K)
/-- The source localization `k[u,v]_{v²}`. -/
abbrev SourceZ := Localization.Away (Cusp.coneParam K (coneZ K))

/-- The localized cone map over `D(x)`. -/
def chartX : TargetX K →ₐ[K] SourceX K :=
  IsLocalization.Away.mapₐ (TargetX K) (SourceX K) (Cusp.coneParam K) (coneX K)

/-- The localized cone map over `D(z)`. -/
def chartZ : TargetZ K →ₐ[K] SourceZ K :=
  IsLocalization.Away.mapₐ (TargetZ K) (SourceZ K) (Cusp.coneParam K) (coneZ K)

instance chartXAlgebra : Algebra (TargetX K) (SourceX K) := (chartX K).toRingHom.toAlgebra
instance chartZAlgebra : Algebra (TargetZ K) (SourceZ K) := (chartZ K).toRingHom.toAlgebra

theorem chartX_on_cone_coordinate (a : ConeRing K) :
    chartX K (algebraMap (ConeRing K) (TargetX K) a) =
      algebraMap (SourceRing K) (SourceX K) (Cusp.coneParam K a) := by
  simp [chartX, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map]

theorem chartZ_on_cone_coordinate (a : ConeRing K) :
    chartZ K (algebraMap (ConeRing K) (TargetZ K) a) =
      algebraMap (SourceRing K) (SourceZ K) (Cusp.coneParam K a) := by
  simp [chartZ, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map]

/-- The localized map over `D(x)` as a morphism of affine schemes. -/
def schemeChartX : Spec (.of (SourceX K)) ⟶ Spec (.of (TargetX K)) :=
  Spec.map (CommRingCat.ofHom (chartX K).toRingHom)

/-- The localized map over `D(z)` as a morphism of affine schemes. -/
def schemeChartZ : Spec (.of (SourceZ K)) ⟶ Spec (.of (TargetZ K)) :=
  Spec.map (CommRingCat.ofHom (chartZ K).toRingHom)

/-- The restriction of `coneMap` over `D(x)` is the localized map. -/
def coneRestrictXIso :
    Arrow.mk (coneMap K ∣_ PrimeSpectrum.basicOpen (coneX K)) ≅ Arrow.mk (schemeChartX K) :=
  SpecMapRestrictBasicOpenIso (CommRingCat.ofHom (Cusp.coneParam K).toRingHom) (coneX K)

/-- The restriction of `coneMap` over `D(z)` is the localized map. -/
def coneRestrictZIso :
    Arrow.mk (coneMap K ∣_ PrimeSpectrum.basicOpen (coneZ K)) ≅ Arrow.mk (schemeChartZ K) :=
  SpecMapRestrictBasicOpenIso (CommRingCat.ofHom (Cusp.coneParam K).toRingHom) (coneZ K)

/-! ### The standard étale pair of `T² - a` -/

variable {K} in
/-- The standard étale pair `(T² - a, 1)` when `a` and `2` are units. -/
def standardQuadraticPair {R : Type*} [CommRing R] (a : Rˣ) (h2 : IsUnit (2 : R)) :
    StandardEtalePair R := by
  let f : R[X] := X ^ 2 - C (a : R)
  have hmonic : f.Monic := by
    simpa only [f] using Polynomial.monic_X_pow_sub_C (a : R) (by decide : 2 ≠ 0)
  have hsep : f.Separable := Polynomial.separable_X_pow_sub_C_unit a h2
  let w := (Polynomial.separable_def' f).mp hsep
  let p2 := w.choose
  let p1 := w.choose_spec.choose
  have hbez : p2 * f + p1 * f.derivative = 1 := w.choose_spec.choose_spec
  exact ⟨f, hmonic, 1, p1, p2, 0, by
    rw [pow_zero]
    calc
      _ = p2 * f + p1 * f.derivative := by ring
      _ = 1 := hbez⟩

variable {K} in
/-- A standard étale pair with `g = 1` is the plain quotient `R[T]/(f)`. -/
def standardPairEquivAdjoinRoot {R : Type*} [CommRing R] (P : StandardEtalePair R)
    (h : P.g = 1) : P.Ring ≃ₐ[R] AdjoinRoot P.f := by
  have hunit : IsUnit (AdjoinRoot.mk P.f P.g) := by rw [h]; simp
  exact P.equivAwayAdjoinRoot.trans
    (((IsLocalization.atUnit (AdjoinRoot P.f)
      (Localization.Away (AdjoinRoot.mk P.f P.g))
      (AdjoinRoot.mk P.f P.g) hunit).symm).restrictScalars R)

end Pcf.Examples.CharZeroPaperConeBranch

#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneY
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneY_sq
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneParam_x
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneParam_y
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneParam_z
#print axioms Pcf.Examples.CharZeroPaperConeBranch.negBoth
#print axioms Pcf.Examples.CharZeroPaperConeBranch.negBoth_X0
#print axioms Pcf.Examples.CharZeroPaperConeBranch.negBoth_X1
#print axioms Pcf.Examples.CharZeroPaperConeBranch.negBoth_expand
#print axioms Pcf.Examples.CharZeroPaperConeBranch.negBoth_coneParam
#print axioms Pcf.Examples.CharZeroPaperConeBranch.plane_decomposition
#print axioms Pcf.Examples.CharZeroPaperConeBranch.negBoth_fixed_iff
#print axioms Pcf.Examples.CharZeroPaperConeBranch.cone_isIntegrallyClosed
#print axioms Pcf.Examples.CharZeroPaperConeBranch.sub_constantCoeff_mem
#print axioms Pcf.Examples.CharZeroPaperConeBranch.vertexEval
#print axioms Pcf.Examples.CharZeroPaperConeBranch.vertexEval_mk
#print axioms Pcf.Examples.CharZeroPaperConeBranch.mem_vertex_iff
#print axioms Pcf.Examples.CharZeroPaperConeBranch.vertex_eq_ker
#print axioms Pcf.Examples.CharZeroPaperConeBranch.vertex_isMaximal
#print axioms Pcf.Examples.CharZeroPaperConeBranch.vertexLocus
#print axioms Pcf.Examples.CharZeroPaperConeBranch.mem_vertexLocus_iff
#print axioms Pcf.Examples.CharZeroPaperConeBranch.planeOrigin
#print axioms Pcf.Examples.CharZeroPaperConeBranch.planeOrigin_isMaximal
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coordinates_mem_iff_planeOrigin
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneMap_eq_vertex_iff
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneMap_preimage_vertex
#print axioms Pcf.Examples.CharZeroPaperConeBranch.plane_heightOne_not_both_coordinates
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneMap_divisor_ne_vertex
#print axioms Pcf.Examples.CharZeroPaperConeBranch.sourceLineIdeal
#print axioms Pcf.Examples.CharZeroPaperConeBranch.targetLineIdeal
#print axioms Pcf.Examples.CharZeroPaperConeBranch.sourceLineQuotientEquiv
#print axioms Pcf.Examples.CharZeroPaperConeBranch.targetLineQuotientEquiv
#print axioms Pcf.Examples.CharZeroPaperConeBranch.sourceLinePullback_ker
#print axioms Pcf.Examples.CharZeroPaperConeBranch.targetLinePullback_ker
#print axioms Pcf.Examples.CharZeroPaperConeBranch.sourceLine_range
#print axioms Pcf.Examples.CharZeroPaperConeBranch.targetLine_range
#print axioms Pcf.Examples.CharZeroPaperConeBranch.targetLineIdeal_isPrime
#print axioms Pcf.Examples.CharZeroPaperConeBranch.puncturedOpen
#print axioms Pcf.Examples.CharZeroPaperConeBranch.mem_puncturedOpen_iff_ne_vertex
#print axioms Pcf.Examples.CharZeroPaperConeBranch.mem_basicOpen_x_or_z
#print axioms Pcf.Examples.CharZeroPaperConeBranch.TargetX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.SourceX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.TargetZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.SourceZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.chartX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.chartZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.chartXAlgebra
#print axioms Pcf.Examples.CharZeroPaperConeBranch.chartZAlgebra
#print axioms Pcf.Examples.CharZeroPaperConeBranch.chartX_on_cone_coordinate
#print axioms Pcf.Examples.CharZeroPaperConeBranch.chartZ_on_cone_coordinate
#print axioms Pcf.Examples.CharZeroPaperConeBranch.schemeChartX
#print axioms Pcf.Examples.CharZeroPaperConeBranch.schemeChartZ
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneRestrictXIso
#print axioms Pcf.Examples.CharZeroPaperConeBranch.coneRestrictZIso
#print axioms Pcf.Examples.CharZeroPaperConeBranch.standardQuadraticPair
#print axioms Pcf.Examples.CharZeroPaperConeBranch.standardPairEquivAdjoinRoot
