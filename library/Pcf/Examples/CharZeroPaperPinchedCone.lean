module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Algebraic support for `paper.tex`, `ex:pinched` and `ex:branch-singular`

These results use the actual polynomial equations. No branch/PCF conclusion or
identification of a scheme with an abstract dynamical model is assumed.
-/

@[expose] public section

namespace Pcf.Examples.CharZeroPaperPinchedCone

variable {K : Type*} [Field K]

/-- The nodal parametrization in `ex:pinched`, in coordinates `(b,d)`. -/
def nodeParam (z : K) : K × K := (z ^ 2, z * (z ^ 2 - 4))

/-- The displayed restriction map in the nodal plane presentation. -/
def nodeMap (p : K × K) : K × K := (p.1 ^ 2, p.1 ^ 3 - 4 * p.1)

theorem nodeParam_relation (z : K) :
    (nodeParam z).2 ^ 2 = (nodeParam z).1 * ((nodeParam z).1 - 4) ^ 2 := by
  simp [nodeParam]
  ring

theorem nodeMap_relation (p : K × K) :
    (nodeMap p).2 ^ 2 = (nodeMap p).1 * ((nodeMap p).1 - 4) ^ 2 := by
  simp [nodeMap]
  ring

/-- Squaring on the normalization agrees with the displayed nodal map. -/
theorem nodeParam_semiconjugacy (z : K) :
    nodeParam (z ^ 2) = nodeMap (nodeParam z) := by
  apply Prod.ext
  · rfl
  · dsimp [nodeParam, nodeMap]; ring

theorem nodeParam_four : nodeParam (4 : K) = (16, 48) := by
  norm_num [nodeParam]

theorem nodeMap_pinched_point : nodeMap ((4 : K), 0) = (16, 48) := by
  norm_num [nodeMap]

open MvPolynomial

/-- The equations of the fibre over `(b,d)=(16,48)` in the nodal presentation. -/
noncomputable def nodeFiberIdeal (K : Type*) [Field K] : Ideal (MvPolynomial (Fin 2) K) :=
  Ideal.span {X 1 ^ 2 - X 0 * (X 0 - 4) ^ 2, X 0 ^ 2 - 16, X 0 ^ 3 - 4 * X 0 - 48}

/-- Exact elimination in the fibre ideal: `(relation, b²-16, b³-4b-48)=(b-4,d²)`. -/
theorem nodeFiberIdeal_eq [CharZero K] :
    nodeFiberIdeal K = Ideal.span {X 0 - 4, (X 1 : MvPolynomial (Fin 2) K) ^ 2} := by
  let I := nodeFiberIdeal K
  let J : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {X 0 - 4, X 1 ^ 2}
  have hbJ : X 0 - 4 ∈ J := Ideal.subset_span (by simp)
  have hdJ : X 1 ^ 2 ∈ J := Ideal.subset_span (by simp)
  have hrI : X 1 ^ 2 - X 0 * (X 0 - 4) ^ 2 ∈ I := Ideal.subset_span (by simp)
  have hbI : X 0 ^ 2 - 16 ∈ I := Ideal.subset_span (by simp)
  have hgI : X 0 ^ 3 - 4 * X 0 - 48 ∈ I := Ideal.subset_span (by simp)
  have hlin : X 0 - 4 ∈ I := by
    have h := I.sub_mem hgI (I.mul_mem_left (X 0) hbI)
    have h' := I.mul_mem_left (C ((12 : K)⁻¹)) h
    have heq : C ((12 : K)⁻¹) *
        (X 0 ^ 3 - 4 * X 0 - 48 - X 0 * (X 0 ^ 2 - 16)) =
        (X 0 - 4 : MvPolynomial (Fin 2) K) := by
      calc
        (C ((12 : K)⁻¹) : MvPolynomial (Fin 2) K) *
            (X 0 ^ 3 - 4 * X 0 - 48 - X 0 * (X 0 ^ 2 - 16)) =
            (C ((12 : K)⁻¹) * 12) * (X 0 - 4) := by ring
        _ = (C ((12 : K)⁻¹) * C (12 : K)) * (X 0 - 4) := by rw [map_ofNat C 12]
        _ = X 0 - 4 := by rw [← map_mul]; norm_num
    rwa [heq] at h'
  have hdI : X 1 ^ 2 ∈ I := by
    have h := I.add_mem hrI (I.mul_mem_left (X 0 * (X 0 - 4)) hlin)
    convert h using 1; ring
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro p hp
    rcases hp with rfl | rfl | rfl
    · change X 1 ^ 2 - X 0 * (X 0 - 4) ^ 2 ∈ J
      have h := J.sub_mem hdJ (J.mul_mem_left (X 0 * (X 0 - 4)) hbJ)
      convert h using 1; ring
    · change X 0 ^ 2 - 16 ∈ J
      have h := J.mul_mem_left (X 0 + 4) hbJ
      convert h using 1; ring
    · change X 0 ^ 3 - 4 * X 0 - 48 ∈ J
      have h := J.mul_mem_left (X 0 ^ 2 + 4 * X 0 + 12) hbJ
      convert h using 1; ring
  · exact Ideal.span_le.mpr (by intro p hp; rcases hp with rfl | rfl; exact hlin; exact hdI)

/-- The algebra explicitly presented by the fibre equations; its scheme-fibre bridge is separate. -/
abbrev NodeFiber (K : Type*) [Field K] := MvPolynomial (Fin 2) K ⧸ nodeFiberIdeal K

theorem nodeFiber_b_eq_four [CharZero K] :
    Ideal.Quotient.mk (nodeFiberIdeal K) (X 0) = (4 : NodeFiber K) := by
  apply sub_eq_zero.mp
  rw [← map_ofNat (Ideal.Quotient.mk (nodeFiberIdeal K)) 4, ← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [nodeFiberIdeal_eq]
  exact Ideal.subset_span (by simp)

theorem nodeFiber_d_sq [CharZero K] :
    (Ideal.Quotient.mk (nodeFiberIdeal K) (X 1)) ^ 2 = 0 := by
  rw [← map_pow]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [nodeFiberIdeal_eq]
  exact Ideal.subset_span (by simp)

/-- Evaluate the fibre algebra in the dual numbers by `b↦4`, `d↦ε`. -/
noncomputable def nodeFiberToDual [CharZero K] : NodeFiber K →ₐ[K] DualNumber K :=
  Ideal.Quotient.liftₐ _ (aeval ![4, DualNumber.eps]) <| by
    intro p hp
    rw [nodeFiberIdeal_eq] at hp
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hp
    simp [DualNumber.eps_pow_two]

@[simp] theorem nodeFiberToDual_d [CharZero K] :
    nodeFiberToDual (Ideal.Quotient.mk (nodeFiberIdeal K) (X 1)) = DualNumber.eps := by
  change aeval ![(4 : DualNumber K), DualNumber.eps] (X 1) = _
  simp

/-- The square-zero coordinate is genuinely nonzero in the displayed fibre algebra. -/
theorem nodeFiber_d_ne_zero [CharZero K] :
    Ideal.Quotient.mk (nodeFiberIdeal K) (X 1) ≠ 0 := by
  intro h
  have he := congrArg (nodeFiberToDual (K := K)) h
  simp only [nodeFiberToDual_d, map_zero] at he
  have hs := congrArg TrivSqZeroExt.snd he
  simp at hs

/-- Nonreducedness is proved for the actual quotient by the fibre equations. -/
theorem nodeFiber_not_isReduced [CharZero K] : ¬ IsReduced (NodeFiber K) := by
  intro h
  let := h
  exact nodeFiber_d_ne_zero (K := K) (IsNilpotent.eq_zero ⟨2, nodeFiber_d_sq⟩)

/-- The converse algebra map sends the dual-number infinitesimal to the class of `d`. -/
noncomputable def dualToNodeFiber [CharZero K] : DualNumber K →ₐ[K] NodeFiber K :=
  DualNumber.lift ⟨(Algebra.ofId K _, Ideal.Quotient.mk (nodeFiberIdeal K) (X 1)),
    by simpa [pow_two] using (nodeFiber_d_sq (K := K)), fun _ => Commute.all _ _⟩

@[simp] theorem dualToNodeFiber_eps [CharZero K] :
    dualToNodeFiber (DualNumber.eps : DualNumber K) =
      Ideal.Quotient.mk (nodeFiberIdeal K) (X 1) := by
  simp [dualToNodeFiber]

/-- The presented fibre is exactly the dual-number algebra, not merely nonreduced. -/
noncomputable def nodeFiberEquivDual [CharZero K] : NodeFiber K ≃ₐ[K] DualNumber K :=
  AlgEquiv.ofAlgHom nodeFiberToDual dualToNodeFiber
    (by apply DualNumber.algHom_ext; simp)
    (by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i
      · change dualToNodeFiber (aeval ![(4 : DualNumber K), DualNumber.eps] (X 0)) =
          Ideal.Quotient.mk (nodeFiberIdeal K) (X 0)
        simp [nodeFiber_b_eq_four]
        exact map_ofNat (dualToNodeFiber (K := K)) 4
      · change dualToNodeFiber (aeval ![(4 : DualNumber K), DualNumber.eps] (X 1)) =
          Ideal.Quotient.mk (nodeFiberIdeal K) (X 1)
        simp)

/-- The quadratic map to the cone in `ex:branch-singular`. -/
def coneMap (p : K × K) : Fin 3 → K := ![p.1 ^ 2, p.1 * p.2, p.2 ^ 2]

/-- The quadric cone as a set of field-valued points. -/
def cone : Set (Fin 3 → K) := {v | v 0 * v 2 = v 1 ^ 2}

theorem coneMap_mem (p : K × K) : coneMap p ∈ cone := by
  change p.1 ^ 2 * p.2 ^ 2 = (p.1 * p.2) ^ 2
  ring

/-- Surjectivity onto the cone is proved by explicit square roots and division. -/
theorem coneMap_range [IsAlgClosed K] : Set.range (coneMap (K := K)) = cone := by
  ext v
  constructor
  · rintro ⟨p, rfl⟩
    exact coneMap_mem p
  · intro hv
    change v 0 * v 2 = v 1 ^ 2 at hv
    by_cases hx : v 0 = 0
    · have hy : v 1 = 0 := by simpa [hx] using hv.symm
      obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (v 2) (n := 2) (by decide)
      refine ⟨(0, b), ?_⟩
      funext i
      fin_cases i <;> simp [coneMap, hx, hy, hb]
    · obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (v 0) (n := 2) (by decide)
      have ha0 : a ≠ 0 := by intro h; simp [h] at ha; exact hx ha.symm
      refine ⟨(a, v 1 / a), ?_⟩
      funext i
      fin_cases i
      · simpa [coneMap] using ha
      · change a * (v 1 / a) = v 1
        field_simp
      · change (v 1 / a) ^ 2 = v 2
        rw [div_pow, ha, ← hv]
        field_simp

/-- The only point over the vertex is the origin. -/
theorem coneMap_eq_zero_iff (p : K × K) : coneMap p = 0 ↔ p = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h2 := congrFun h 2
    apply Prod.ext
    · simpa [coneMap] using h0
    · simpa [coneMap] using h2
  · rintro rfl
    funext i
    fin_cases i <;> simp [coneMap]

/-- Exact point-image of the restricted divisor `A=V(v)` in `ex:branch-singular`. -/
theorem coneMap_axis_image [IsAlgClosed K] :
    coneMap '' {p : K × K | p.2 = 0} = {v | v 1 = 0 ∧ v 2 = 0} := by
  ext v
  constructor
  · rintro ⟨p, hp, rfl⟩
    change p.2 = 0 at hp
    simp [coneMap, hp]
  · rintro ⟨h1, h2⟩
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (v 0) (n := 2) (by decide)
    refine ⟨(a, 0), rfl, ?_⟩
    funext i
    fin_cases i <;> simp [coneMap, ha, h1, h2]

/-- The map is unchanged under simultaneous negation. -/
theorem coneMap_neg (p : K × K) : coneMap (-p) = coneMap p := by
  funext i
  fin_cases i <;> simp [coneMap]

/-- Exact classification of field-valued fibres: two points differ by simultaneous sign. -/
theorem coneMap_eq_iff (p q : K × K) :
    coneMap p = coneMap q ↔ p = q ∨ p = -q := by
  rcases p with ⟨u, v⟩
  rcases q with ⟨a, b⟩
  constructor
  · intro h
    have h0 : u ^ 2 = a ^ 2 := congrFun h 0
    have h1 : u * v = a * b := congrFun h 1
    have h2 : v ^ 2 = b ^ 2 := congrFun h 2
    by_cases hu : u = 0
    · subst u
      have ha : a = 0 := by simpa using h0.symm
      subst a
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with hv | hv
      · exact Or.inl (by simp [hv])
      · exact Or.inr (by simp [hv])
    · rcases sq_eq_sq_iff_eq_or_eq_neg.mp h0 with hua | hua
      · have hvb : v = b := mul_left_cancel₀ hu (by simpa [← hua] using h1)
        exact Or.inl (by simp [hua, hvb])
      · have hvb : v = -b := by
          apply mul_left_cancel₀ hu
          calc
            u * v = a * b := h1
            _ = u * -b := by rw [hua]; ring
        exact Or.inr (by simp [hua, hvb])
  · rintro (h | h)
    · exact congrArg coneMap h
    · rw [h]
      exact coneMap_neg (a, b)

/-- The set cut out by all partial derivatives of `xz-y²` is the vertex in characteristic zero. -/
theorem cone_gradient_zero_iff [CharZero K] (v : Fin 3 → K) :
    (v 2 = 0 ∧ -2 * v 1 = 0 ∧ v 0 = 0) ↔ v = 0 := by
  constructor
  · rintro ⟨h2, h1, h0⟩
    have hy : v 1 = 0 := (mul_eq_zero.mp h1).resolve_left (by norm_num)
    funext i
    fin_cases i <;> simp [h0, hy, h2]
  · rintro rfl
    simp

/-- This computes the polynomial gradient, rather than assuming the displayed entries. -/
theorem cone_polynomial_gradient (i : Fin 3) :
    pderiv i ((X 0 * X 2 - X 1 ^ 2 : MvPolynomial (Fin 3) K)) =
      ![X 2, -2 * X 1, X 0] i := by
  fin_cases i <;> simp [pderiv_X]

/-- Homogeneous polynomials defining the map to the quadric cone. -/
noncomputable def conePolynomial : Fin 3 → MvPolynomial (Fin 2) K :=
  ![X 0 ^ 2, X 0 * X 1, X 1 ^ 2]

/-- Each `2×2` Jacobian minor is computed by actual polynomial differentiation. -/
theorem cone_polynomial_minor (i j : Fin 3) :
    pderiv 0 (conePolynomial (K := K) i) * pderiv 1 (conePolynomial j) -
      pderiv 1 (conePolynomial i) * pderiv 0 (conePolynomial j) =
      !![0, 2 * X 0 ^ 2, 4 * X 0 * X 1;
        -(2 * X 0 ^ 2), 0, 2 * X 1 ^ 2;
        -(4 * X 0 * X 1), -(2 * X 1 ^ 2), 0] i j := by
  fin_cases i <;> fin_cases j <;> simp [conePolynomial, pderiv_X] <;> ring

/-- In characteristic zero the maximal minors vanish simultaneously only at the origin. -/
theorem cone_minors_zero_iff [CharZero K] (u v : K) :
    (2 * u ^ 2 = 0 ∧ 4 * u * v = 0 ∧ 2 * v ^ 2 = 0) ↔ u = 0 ∧ v = 0 := by
  constructor
  · rintro ⟨hu, _, hv⟩
    constructor
    · simpa using (mul_eq_zero.mp hu).resolve_left (by norm_num)
    · simpa using (mul_eq_zero.mp hv).resolve_left (by norm_num)
  · rintro ⟨rfl, rfl⟩
    simp

/-- The concrete subalgebra generated by the coordinates of the cone map. -/
noncomputable def coneSubalgebra (K : Type*) [Field K] : Subalgebra K (MvPolynomial (Fin 2) K) :=
  Algebra.adjoin K {X 0 ^ 2, X 0 * X 1, X 1 ^ 2}

/-- Both source coordinates are integral over `k[u²,uv,v²]`. -/
theorem cone_coordinate_isIntegral (i : Fin 2) :
    IsIntegral (coneSubalgebra K) (X i : MvPolynomial (Fin 2) K) := by
  have hm : (X i : MvPolynomial (Fin 2) K) ^ 2 ∈ coneSubalgebra K := by
    apply Algebra.subset_adjoin
    fin_cases i <;> simp
  apply IsIntegral.of_pow (n := 2) (by decide)
  exact isIntegral_algebraMap (x := (⟨X i ^ 2, hm⟩ : coneSubalgebra K))

/-- Every source polynomial is integral over the concrete cone-coordinate subalgebra. -/
theorem cone_polynomial_isIntegral (p : MvPolynomial (Fin 2) K) :
    IsIntegral (coneSubalgebra K) p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    exact isIntegral_algebraMap
      (x := (⟨C a, (coneSubalgebra K).algebraMap_mem a⟩ : coneSubalgebra K))
  | add p q hp hq => exact hp.add hq
  | mul_X p i hp => exact hp.mul (cone_coordinate_isIntegral i)

/-- The inclusion `k[u²,uv,v²] ⊆ k[u,v]` is finite as a ring extension. -/
theorem coneSubalgebra_finite : Module.Finite (coneSubalgebra K) (MvPolynomial (Fin 2) K) := by
  let : Algebra.IsIntegral (coneSubalgebra K) (MvPolynomial (Fin 2) K) :=
    ⟨cone_polynomial_isIntegral⟩
  let : Algebra.FiniteType (coneSubalgebra K) (MvPolynomial (Fin 2) K) :=
    Algebra.FiniteType.of_restrictScalars_finiteType K (coneSubalgebra K) _
  exact Algebra.IsIntegral.finite

end Pcf.Examples.CharZeroPaperPinchedCone

#print axioms Pcf.Examples.CharZeroPaperPinchedCone.nodeParam_relation
#print axioms Pcf.Examples.CharZeroPaperPinchedCone.nodeMap_relation
#print axioms Pcf.Examples.CharZeroPaperPinchedCone.nodeParam_semiconjugacy
#print axioms Pcf.Examples.CharZeroPaperPinchedCone.nodeParam_four
#print axioms Pcf.Examples.CharZeroPaperPinchedCone.nodeMap_pinched_point
#print axioms Pcf.Examples.CharZeroPaperPinchedCone.nodeFiberIdeal_eq
#print axioms Pcf.Examples.CharZeroPaperPinchedCone.nodeFiber_b_eq_four
#print axioms Pcf.Examples.CharZeroPaperPinchedCone.nodeFiber_d_sq
#print axioms Pcf.Examples.CharZeroPaperPinchedCone.nodeFiberToDual_d
#print axioms Pcf.Examples.CharZeroPaperPinchedCone.nodeFiber_d_ne_zero
#print axioms Pcf.Examples.CharZeroPaperPinchedCone.nodeFiber_not_isReduced
#print axioms Pcf.Examples.CharZeroPaperPinchedCone.dualToNodeFiber_eps
#print axioms Pcf.Examples.CharZeroPaperPinchedCone.nodeFiberEquivDual
#print axioms Pcf.Examples.CharZeroPaperPinchedCone.coneMap_mem
#print axioms Pcf.Examples.CharZeroPaperPinchedCone.coneMap_range
#print axioms Pcf.Examples.CharZeroPaperPinchedCone.coneMap_eq_zero_iff
#print axioms Pcf.Examples.CharZeroPaperPinchedCone.coneMap_axis_image
#print axioms Pcf.Examples.CharZeroPaperPinchedCone.coneMap_neg
#print axioms Pcf.Examples.CharZeroPaperPinchedCone.coneMap_eq_iff
#print axioms Pcf.Examples.CharZeroPaperPinchedCone.cone_gradient_zero_iff
#print axioms Pcf.Examples.CharZeroPaperPinchedCone.cone_polynomial_gradient
#print axioms Pcf.Examples.CharZeroPaperPinchedCone.cone_polynomial_minor
#print axioms Pcf.Examples.CharZeroPaperPinchedCone.cone_minors_zero_iff
#print axioms Pcf.Examples.CharZeroPaperPinchedCone.cone_coordinate_isIntegral
#print axioms Pcf.Examples.CharZeroPaperPinchedCone.cone_polynomial_isIntegral
#print axioms Pcf.Examples.CharZeroPaperPinchedCone.coneSubalgebra_finite

-- Full types expose every field hypothesis and the exact algebraic scope.
#check @Pcf.Examples.CharZeroPaperPinchedCone.nodeParam_relation
#check @Pcf.Examples.CharZeroPaperPinchedCone.nodeMap_relation
#check @Pcf.Examples.CharZeroPaperPinchedCone.nodeParam_semiconjugacy
#check @Pcf.Examples.CharZeroPaperPinchedCone.nodeParam_four
#check @Pcf.Examples.CharZeroPaperPinchedCone.nodeMap_pinched_point
#check @Pcf.Examples.CharZeroPaperPinchedCone.nodeFiberIdeal_eq
#check @Pcf.Examples.CharZeroPaperPinchedCone.nodeFiber_b_eq_four
#check @Pcf.Examples.CharZeroPaperPinchedCone.nodeFiber_d_sq
#check @Pcf.Examples.CharZeroPaperPinchedCone.nodeFiberToDual_d
#check @Pcf.Examples.CharZeroPaperPinchedCone.nodeFiber_d_ne_zero
#check @Pcf.Examples.CharZeroPaperPinchedCone.nodeFiber_not_isReduced
#check @Pcf.Examples.CharZeroPaperPinchedCone.dualToNodeFiber_eps
#check @Pcf.Examples.CharZeroPaperPinchedCone.nodeFiberEquivDual
#check @Pcf.Examples.CharZeroPaperPinchedCone.coneMap_mem
#check @Pcf.Examples.CharZeroPaperPinchedCone.coneMap_range
#check @Pcf.Examples.CharZeroPaperPinchedCone.coneMap_eq_zero_iff
#check @Pcf.Examples.CharZeroPaperPinchedCone.coneMap_axis_image
#check @Pcf.Examples.CharZeroPaperPinchedCone.coneMap_neg
#check @Pcf.Examples.CharZeroPaperPinchedCone.coneMap_eq_iff
#check @Pcf.Examples.CharZeroPaperPinchedCone.cone_gradient_zero_iff
#check @Pcf.Examples.CharZeroPaperPinchedCone.cone_polynomial_gradient
#check @Pcf.Examples.CharZeroPaperPinchedCone.cone_polynomial_minor
#check @Pcf.Examples.CharZeroPaperPinchedCone.cone_minors_zero_iff
#check @Pcf.Examples.CharZeroPaperPinchedCone.cone_coordinate_isIntegral
#check @Pcf.Examples.CharZeroPaperPinchedCone.cone_polynomial_isIntegral
#check @Pcf.Examples.CharZeroPaperPinchedCone.coneSubalgebra_finite
