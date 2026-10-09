/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Bounding.GlobalNormalizationIteration
import Pcf.Bounding.InvariantDivisorStep0FiniteType
import Pcf.Bounding.PeriodicLift

/-!
# PCF restriction to periodic divisors of actual schemes

The only mathematical hypotheses left explicit beyond the standing geometric
ones are the local purity and Abhyankar packages.  The local-domain consequence
of regularity is supplied by the proved Stacks Tag 00NP.  The finite regularity correction,
periodic lift, induced finite cover between reduced divisor closures, and PCF
descent are constructed from the actual scheme morphisms.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

set_option linter.style.haveILetI false

/-- PCF on the canonical normalization, with the characteristic-zero structure
obtained from the actual structure morphism. The normalization PCF equivalence
identifies this with the paper's normalized branch-locus definition. -/
def SchemeNormalizedPCFOfFiniteType
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] : Prop := by
  letI := schemeStalkCharZeroOfField k s (genericPoint X)
  exact (schemeGlobalNormalizationUnnormDynOfFiniteType k s f).norm.PCF

/-- This presentation measures the actual lifted morphism on the actual global
normalization; it introduces no substitute dynamics. -/
theorem schemeNormalizedPCFOfFiniteType_iff_lift
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] :
    SchemeNormalizedPCFOfFiniteType k s f ↔
      letI := schemeGlobalNormalizationMap_isFinite X k s
      letI := schemeStalkCharZeroOfField k s (genericPoint X)
      (divDynOfFiniteDominantNormalCharZero (schemeGlobalNormalizationLift f)).PCF :=
  Iff.rfl

/-- Positive iteration does not change canonical normalized PCF. -/
theorem schemeNormalizedPCFOfFiniteType_pow_iff
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (m : ℕ) (hm : 1 ≤ m) :
    SchemeNormalizedPCFOfFiniteType k s (End.of f ^ m) ↔
      SchemeNormalizedPCFOfFiniteType k s f := by
  letI := schemeGlobalNormalizationMap_isFinite X k s
  letI := schemeStalkCharZeroOfField k s (genericPoint X)
  rw [schemeNormalizedPCFOfFiniteType_iff_lift,
    schemeNormalizedPCFOfFiniteType_iff_lift]
  simp only [
    schemeGlobalNormalizationLift_pow,
    divDynOfFiniteDominantNormalCharZero_pow_eq_iter,
    DivDyn.PCF, DivDyn.pcSet_iter _ hm]

/-- Normalized PCF descends along an actual finite dominant commuting cover.
Both structure morphisms are used only to obtain finite normalizations and
characteristic zero; compatibility of those structure morphisms is unnecessary. -/
theorem schemeNormalizedPCFOfFiniteType_of_cover
    (k : Type u) [Field k] [CharZero k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
    (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsFinite π] [IsDominant π]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [NoetherianSpace Y]
    (hcomm : g ≫ π = π ≫ f)
    (hpcf : SchemeNormalizedPCFOfFiniteType k sY g) :
    SchemeNormalizedPCFOfFiniteType k sX f := by
  letI := schemeGlobalNormalizationMap_isFinite X k sX
  letI := schemeGlobalNormalizationMap_isFinite Y k sY
  letI := schemeStalkCharZeroOfField k sX (genericPoint X)
  letI := schemeStalkCharZeroOfField k sY (genericPoint Y)
  exact scheme_pcf_of_ramified_cover_charZero
    (schemeGlobalNormalizationLift f) (schemeGlobalNormalizationLift g)
    (schemeGlobalNormalizationMorphism π)
    (schemeGlobalNormalizationMorphism_comm f g π hcomm) hpcf

/-- The square on reduced point closures induced by an ambient commuting square. -/
theorem pointClosureSubschemeMap_comm
    {X Y : Scheme.{u}} (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    (hcomm : g ≫ π = π ≫ f) (x : X) (y : Y)
    (hx : f x = x) (hy : g y = y) (hπ : π y = x) :
    pointClosureSubschemeMap g y y hy ≫ pointClosureSubschemeMap π y x hπ =
      pointClosureSubschemeMap π y x hπ ≫ pointClosureSubschemeMap f x x hx := by
  apply (cancel_mono (pointClosureIdealSheaf x).subschemeι).mp
  simp only [Category.assoc, pointClosureSubschemeMap_subschemeι,
    pointClosureSubschemeMap_subschemeι_assoc, hcomm]

/-- A commuting square remains commuting after iterating both endomorphisms. -/
theorem schemeEnd_pow_comm
    {X Y : Scheme.{u}} (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    (hcomm : g ≫ π = π ≫ f) (m : ℕ) :
    (End.of g ^ m) ≫ π = π ≫ (End.of f ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [pow_succ, End.mul_def, Category.assoc]
      rw [ih, ← Category.assoc, hcomm, Category.assoc]

/-- The two local covering packages needed for one invariant divisor, on every
actual iterate and affine preimage chart. -/
def InvariantDivisorCoveringInputs
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] (A : SchemeDivisorPoint X) : Prop :=
  ∀ (m : ℕ) (U : X.affineOpens)
    (Q' : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme)
    (hx : Q'.1 ∈ (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
      (finitePreimageAffine (End.of f ^ m) U : X.Opens)),
    InvariantDivisorLocalCoveringInputs f A m U Q' hx

/-- Affine field-algebra structures supplied by an actual structure morphism. -/
@[instance_reducible]
def schemeAffineAlgebraOfField
    (k : Type u) [Field k] {X : Scheme.{u}} (s : X ⟶ Spec (.of k))
    (U : X.affineOpens) : Algebra k Γ(X, U) :=
  ((s.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra

/-- These affine field algebras are finite type under the geometric hypothesis. -/
theorem schemeAffineAlgebraOfField_finiteType
    (k : Type u) [Field k] {X : Scheme.{u}} (s : X ⟶ Spec (.of k))
    [LocallyOfFiniteType s] (U : X.affineOpens) :
    letI := schemeAffineAlgebraOfField k s U
    Algebra.FiniteType k Γ(X, U) := by
  letI := schemeAffineAlgebraOfField k s U
  apply RingHom.finiteType_algebraMap.mp
  exact (s.finiteType_appLE (isAffineOpen_top _) U.2 (by simp)).comp
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.finite.finiteType

/-- The structure-morphism presentation agrees with normalized branch-locus PCF,
even when the affine algebra instances were supplied separately. -/
theorem schemeNormalizedPCFOfFiniteType_iff
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    [CharZero (X.presheaf.stalk (genericPoint X))]
    [∀ U : X.affineOpens, Algebra k Γ(X, U)]
    [∀ U : X.affineOpens, Algebra.FiniteType k Γ(X, U)] :
    SchemeNormalizedPCFOfFiniteType k s f ↔ SchemeNormalizedPCF k f :=
  (schemeNormalizedPCF_iff_normalization k f).symm

/-- The invariant-divisor theorem stated directly for normalized PCF of its
actual restriction morphism. -/
theorem invariantDivisor_schemeNormalizedPCFOfFiniteType
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X] [NoetherianSpace X]
    (A : SchemeDivisorPoint X) (hA : f A.1 = A.1)
    (cover : InvariantDivisorCoveringInputs f A)
    (hpcf : letI := schemeStalkCharZeroOfField k s (genericPoint X)
      (divDynOfFiniteDominantNormalCharZero f).PCF) :
    SchemeNormalizedPCFOfFiniteType k ((pointClosureIdealSheaf A.1).subschemeι ≫ s)
      (A.invariantClosureMap f hA) :=
  invariantDivisorNormalization_norm_pcf_of_finiteType
    k s f A hA cover hpcf

/-- The general periodic-divisor theorem. The ambient scheme need not be normal.
The only extra mathematical inputs are the explicit local purity and Abhyankar
packages on the canonical normalization. -/
theorem periodicDivisor_schemeNormalizedPCFOfFiniteType
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (A : SchemeDivisorPoint X) (p : ℕ) (hp : 1 ≤ p)
    (hA : (End.of f ^ p).base A.1 = A.1)
    (cover : letI := schemeGlobalNormalizationMap_isFinite X k s
      ∀ (n : ℕ) (B : SchemeDivisorPoint (schemeGlobalNormalization X)),
        InvariantDivisorCoveringInputs (End.of (schemeGlobalNormalizationLift f) ^ n) B)
    (hpcf : SchemeNormalizedPCFOfFiniteType k s f) :
    SchemeNormalizedPCFOfFiniteType k ((pointClosureIdealSheaf A.1).subschemeι ≫ s)
      (A.invariantClosureMap (End.of f ^ p) hA) := by
  letI := schemeGlobalNormalizationMap_isFinite X k s
  letI := schemeStalkCharZeroOfField k s (genericPoint X)
  letI (U : X.affineOpens) := schemeAffineAlgebraOfField k s U
  letI (U : X.affineOpens) := schemeAffineAlgebraOfField_finiteType k s U
  let N := schemeGlobalNormalization X
  let ν : N ⟶ X := schemeGlobalNormalizationMap X
  let F : N ⟶ N := schemeGlobalNormalizationLift f
  let sN := ν ≫ s
  have hperiod : (schemeDivisorMap f (coheight_apply_eq_one_of_finiteType f k))^[p] A = A := by
    apply Subtype.ext
    exact (schemeDivisorMap_iterate_val f _ p A).trans hA
  obtain ⟨B, hB, c, hc, hperiodB⟩ := exists_periodic_normalization_divisor k
    f F ν (schemeGlobalNormalizationLift_comp f) A p hperiod
  have hν : ν B.1 = A.1 := congrArg Subtype.val hB
  have hF : (End.of F ^ (p * c)).base B.1 = B.1 :=
    (schemeDivisorMap_iterate_val F _ (p * c) B).symm.trans
      (congrArg Subtype.val hperiodB)
  have hpcfF : (divDynOfFiniteDominantNormalCharZero F).PCF := hpcf
  have hpcfPower : (divDynOfFiniteDominantNormalCharZero (End.of F ^ (p * c))).PCF := by
    rw [divDynOfFiniteDominantNormalCharZero_pow_eq_iter]
    exact (DivDyn.pcf_iter_iff _).mp hpcfF (p * c) (Nat.mul_pos hp hc)
  have hpcfB := invariantDivisor_schemeNormalizedPCFOfFiniteType k sN
    (End.of F ^ (p * c)) B hF (cover (p * c) B) hpcfPower
  let g := A.invariantClosureMap (End.of f ^ p) hA
  let gB := B.invariantClosureMap (End.of F ^ (p * c)) hF
  let π := pointClosureSubschemeMap ν B.1 A.1 hν
  letI : IsFinite π := pointClosureSubschemeMap_isFinite ν B.1 A.1 hν
  letI : IsDominant π := pointClosureSubschemeMap_isDominant ν B.1 A.1 hν
  have hpower : End.of g ^ c =
      pointClosureSubschemeMap (End.of f ^ (p * c)) A.1 A.1
        (by simpa only [pow_mul] using (end_pow_apply_eq_of_apply_eq
          (End.of f ^ p) A.1 hA c)) := by
    rw [A.invariantClosureMap_iterate]
    simp only [← pow_mul]
  have hcomm : gB ≫ π = π ≫ (End.of g ^ c) := by
    rw [hpower]
    exact pointClosureSubschemeMap_comm (End.of f ^ (p * c))
      (End.of F ^ (p * c)) ν
      (schemeEnd_pow_comm f F ν (schemeGlobalNormalizationLift_comp f) (p * c))
      A.1 B.1 _ hF hν
  have hdesc := schemeNormalizedPCFOfFiniteType_of_cover k
    ((pointClosureIdealSheaf A.1).subschemeι ≫ s)
    ((pointClosureIdealSheaf B.1).subschemeι ≫ sN)
    (End.of g ^ c) gB π hcomm hpcfB
  exact (schemeNormalizedPCFOfFiniteType_pow_iff k _ g c (by omega)).mp hdesc

/-- The actual codimension-one point of the image divisor `f^r(A)`. -/
def schemeDivisorIterateOfFiniteType
    (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X]
    (r : ℕ) (A : SchemeDivisorPoint X) : SchemeDivisorPoint X := by
  letI (U : X.affineOpens) := schemeAffineAlgebraOfField k s U
  letI (U : X.affineOpens) := schemeAffineAlgebraOfField_finiteType k s U
  exact schemeDivisorMap (End.of f ^ r)
    (coheight_apply_eq_one_of_finiteType (End.of f ^ r) k) A

@[simp]
theorem schemeDivisorIterateOfFiniteType_val
    (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X]
    (r : ℕ) (A : SchemeDivisorPoint X) :
    (schemeDivisorIterateOfFiniteType k s f r A).1 = (End.of f ^ r).base A.1 := rfl

/-- The preperiodicity relation makes the actual image divisor periodic. -/
theorem schemeDivisorIterateOfFiniteType_periodic
    (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X]
    (r p : ℕ) (A : SchemeDivisorPoint X)
    (hA : (End.of f ^ (r + p)).base A.1 = (End.of f ^ r).base A.1) :
    (End.of f ^ p).base (schemeDivisorIterateOfFiniteType k s f r A).1 =
      (schemeDivisorIterateOfFiniteType k s f r A).1 := by
  rw [Nat.add_comm r p, pow_add] at hA
  exact hA

/-- Scheme-level `thm:general`: the normalized restriction of `f^p` to the
actual image divisor `f^r(A)` is PCF. Normality of `X` is not assumed. Beyond
the standing geometric and PCF hypotheses, only the local purity and Abhyankar
packages are inputs. -/
theorem pcfAllTheWayDown_scheme
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (A : SchemeDivisorPoint X) (r p : ℕ) (hp : 1 ≤ p)
    (hA : (End.of f ^ (r + p)).base A.1 = (End.of f ^ r).base A.1)
    (cover : letI := schemeGlobalNormalizationMap_isFinite X k s
      ∀ (n : ℕ) (B : SchemeDivisorPoint (schemeGlobalNormalization X)),
        InvariantDivisorCoveringInputs (End.of (schemeGlobalNormalizationLift f) ^ n) B)
    (hpcf : SchemeNormalizedPCFOfFiniteType k s f) :
    let B := schemeDivisorIterateOfFiniteType k s f r A
    SchemeNormalizedPCFOfFiniteType k ((pointClosureIdealSheaf B.1).subschemeι ≫ s)
      (B.invariantClosureMap (End.of f ^ p)
        (schemeDivisorIterateOfFiniteType_periodic k s f r p A hA)) :=
  periodicDivisor_schemeNormalizedPCFOfFiniteType k s f
    (schemeDivisorIterateOfFiniteType k s f r A) p hp
    (schemeDivisorIterateOfFiniteType_periodic k s f r p A hA)
    cover hpcf

#print axioms SchemeNormalizedPCFOfFiniteType
#print axioms schemeNormalizedPCFOfFiniteType_iff_lift
#print axioms schemeNormalizedPCFOfFiniteType_pow_iff
#print axioms schemeNormalizedPCFOfFiniteType_of_cover
#print axioms pointClosureSubschemeMap_comm
#print axioms schemeEnd_pow_comm
#print axioms InvariantDivisorCoveringInputs
#print axioms schemeAffineAlgebraOfField
#print axioms schemeAffineAlgebraOfField_finiteType
#print axioms schemeNormalizedPCFOfFiniteType_iff
#print axioms invariantDivisor_schemeNormalizedPCFOfFiniteType
#print axioms periodicDivisor_schemeNormalizedPCFOfFiniteType
#print axioms schemeDivisorIterateOfFiniteType
#print axioms schemeDivisorIterateOfFiniteType_val
#print axioms schemeDivisorIterateOfFiniteType_periodic
#print axioms pcfAllTheWayDown_scheme
#check @pcfAllTheWayDown_scheme

end

end Pcf
