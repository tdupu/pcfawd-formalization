/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingNormalization

/-!
# Closed supports of integral effective divisors

The representation bridge for `paper.tex`, Proposition `prop:pcf-equiv` (3).
The union of the closures of a set of codimension-one points determines that
set uniquely. Finite morphisms carry these unions to the unions defined by
the actual divisor pushforward. Thus the already checked component-set
preperiodicity is equivalent to the manuscript's equality of closed supports.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf.PaperCharZero

variable {X Y : Scheme.{u}}

/-- The union of the underlying closed sets of integral effective divisors.
For a finite set of divisors this is a closed set. -/
def divisorSupport (S : Set (SchemeDivisorPoint X)) : Set X :=
  ⋃ Q ∈ S, closure ({Q.1} : Set X)

/-- A codimension-one point lies in the closure of another such point exactly
when they are equal; strict specialization increases codimension. -/
theorem divisor_mem_closure_iff (P Q : SchemeDivisorPoint X) :
    P.1 ∈ closure ({Q.1} : Set X) ↔ P = Q := by
  constructor
  · intro h
    have hle : P.1 ≤ Q.1 := (specializes_iff_mem_closure).mpr h
    apply Subtype.ext
    by_contra hne
    have hlt : P.1 < Q.1 := lt_iff_le_not_ge.mpr ⟨hle, fun hge =>
      hne (Specializes.antisymm hge hle).eq⟩
    have hc := Order.coheight_strictAnti hlt (by rw [Q.2]; exact ENat.one_lt_top)
    rw [P.2, Q.2] at hc
    exact lt_irrefl _ hc
  · rintro rfl
    exact subset_closure (Set.mem_singleton _)

/-- Recover the divisor set from its union of closed supports. No finiteness
assumption is needed for this direction. -/
theorem mem_divisorSupport_iff (P : SchemeDivisorPoint X) (S : Set (SchemeDivisorPoint X)) :
    P.1 ∈ divisorSupport S ↔ P ∈ S := by
  simp only [divisorSupport, Set.mem_iUnion, divisor_mem_closure_iff]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact hQ
  · intro hP
    exact ⟨P, hP, rfl⟩

/-- Equality of unions of integral effective divisors is equivalent to equality
of their generic-point sets, including the empty set. -/
theorem divisorSupport_eq_iff (S T : Set (SchemeDivisorPoint X)) :
    divisorSupport S = divisorSupport T ↔ S = T := by
  constructor
  · intro h
    ext P
    rw [← mem_divisorSupport_iff P S, ← mem_divisorSupport_iff P T, h]
  · rintro rfl
    rfl

/-- A finite union of divisor supports is closed. -/
theorem isClosed_divisorSupport (S : Set (SchemeDivisorPoint X)) (hS : S.Finite) :
    IsClosed (divisorSupport S) :=
  hS.isClosed_biUnion (fun _ _ => isClosed_closure)

/-- Finite morphisms carry a divisor support to the support of its actual
divisor image. Codimension preservation is the existing geometric input. -/
theorem image_divisorSupport (f : X ⟶ Y) [IsFinite f]
    (hcodim : ∀ Q : SchemeDivisorPoint X, Order.coheight (f Q.1) = 1)
    (S : Set (SchemeDivisorPoint X)) :
    f '' divisorSupport S = divisorSupport (schemeDivisorMap f hcodim '' S) := by
  have hclosure (Q : SchemeDivisorPoint X) :
      f '' closure ({Q.1} : Set X) = closure ({f Q.1} : Set Y) := by
    simpa only [Set.image_singleton] using
      (f.isClosedMap.closure_image_eq_of_continuous f.continuous ({Q.1} : Set X)).symm
  simp only [divisorSupport, Set.image_iUnion, hclosure, Set.biUnion_image,
    schemeDivisorMap_val]

/-- The same compatibility holds for every iterate of the actual morphism. -/
theorem iterate_image_divisorSupport (f : X ⟶ X) [IsFinite f]
    (hcodim : ∀ Q : SchemeDivisorPoint X, Order.coheight (f Q.1) = 1)
    (S : Set (SchemeDivisorPoint X)) (n : ℕ) :
    (fun x : X => f x)^[n] '' divisorSupport S =
      divisorSupport ((schemeDivisorMap f hcodim)^[n] '' S) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← iterate_image, Function.iterate_succ_apply', iterate_image, ih,
      image_divisorSupport f hcodim]
    congr 1
    simp only [Set.image_image, Function.iterate_succ_apply']

section CharacteristicZero

variable (k : Type u) [Field k] [CharZero k]
  {A : Scheme.{u}} (g : A ⟶ A)
  [IsFinite g] [IsDominant g] [LocallyOfFinitePresentation g]
  [IsIntegral A] [IsLocallyNoetherian A] [NoetherianSpace A]
  [CharZero (A.presheaf.stalk (genericPoint A))]
  [∀ U : A.affineOpens, Algebra k Γ(A, U)]
  [∀ U : A.affineOpens, Algebra.FiniteType k Γ(A, U)]

/-- The actual normalized critical divisor set is finite: it lies over the
finite branch set under a finite morphism, whose divisor fibers are finite. -/
theorem schemeNormalizedCriticalDivisors_finite :
    (schemeNormalizedCriticalDivisors k g).Finite := by
  let D := (schemeGlobalNormalizationUnnormalizedDynamics k g).toNormalizationUnnormalizedDynamics
  have hf : (D.step ⁻¹' D.branch).Finite := D.branch_finite.preimage' (fun Q _ =>
    schemeDivisorMap_finite_fiber g (coheight_apply_eq_one_of_finiteType g k) Q)
  apply hf.subset
  intro Q hQ
  exact ⟨Q, hQ, rfl⟩

/-- The union used in the manuscript really is a closed subset of the scheme. -/
theorem isClosed_schemeNormalizedCriticalSupport :
    IsClosed (divisorSupport (schemeNormalizedCriticalDivisors k g)) :=
  isClosed_divisorSupport _ (schemeNormalizedCriticalDivisors_finite k g)

/-- `prop:pcf-equiv`, (1) ⇔ (3), with literal images of the union of the
critical integral effective divisors inside the original scheme.

Manuscript: `prop:pcf-equiv` (Proposition 5.1). -/
theorem scheme_isNormalizedPCF_iff_critical_support_preperiodic : IsNormalizedPCF k g ↔
    ∃ r s : ℕ, 0 < s ∧
      (fun x : A => g x)^[r + s] '' divisorSupport (schemeNormalizedCriticalDivisors k g) =
      (fun x : A => g x)^[r] '' divisorSupport (schemeNormalizedCriticalDivisors k g) := by
  simp only [iterate_image_divisorSupport g (coheight_apply_eq_one_of_finiteType g k),
    divisorSupport_eq_iff]
  exact scheme_isNormalizedPCF_iff_critical_preperiodic k g

end CharacteristicZero
end Pcf.PaperCharZero
