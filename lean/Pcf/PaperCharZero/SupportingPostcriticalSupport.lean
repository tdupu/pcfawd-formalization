/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingClosedSupports

/-!
# The closed support of the normalized postcritical set

The finite set of postcritical integral effective divisors in `paper.tex`
determines a closed union of supports, and the actual finite morphism carries
that union into itself. These statements use the downstairs normalized branch
and postcritical sets of the actual scheme map.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf.PaperCharZero

variable (k : Type u) [Field k] [CharZero k]
  {A : Scheme.{u}} (g : A ⟶ A)
  [IsFinite g] [IsDominant g] [LocallyOfFinitePresentation g]
  [IsIntegral A] [IsLocallyNoetherian A] [NoetherianSpace A]
  [CharZero (A.presheaf.stalk (genericPoint A))]
  [∀ U : A.affineOpens, Algebra k Γ(A, U)]
  [∀ U : A.affineOpens, Algebra.FiniteType k Γ(A, U)]

/-- The postcritical divisors are precisely the positive forward images of
the normalized critical divisors. -/
theorem normalized_postcriticalSet_eq_critical_orbit :
    Pcf.schemeNormalizedPostcriticalSet k g =
      ⋃ n : ℕ,
        (Pcf.schemeDivisorMap g (Pcf.coheight_apply_eq_one_of_finiteType g k))^[n + 1] ''
          schemeNormalizedCriticalDivisors k g := by
  rw [Pcf.schemeNormalizedPostcriticalSet_eq_iUnion]
  change (⋃ n : ℕ,
      (Pcf.schemeDivisorMap g (Pcf.coheight_apply_eq_one_of_finiteType g k))^[n] ''
        ((Pcf.schemeDivisorMap g (Pcf.coheight_apply_eq_one_of_finiteType g k)) ''
          schemeNormalizedCriticalDivisors k g)) = _
  simp only [Set.image_image]
  congr 1

/-- The manuscript's equality of the two unions of closed supports. -/
theorem normalized_postcriticalSupport_eq_critical_orbit :
    divisorSupport (Pcf.schemeNormalizedPostcriticalSet k g) =
      ⋃ n : ℕ, (fun x : A => g x)^[n + 1] ''
        divisorSupport (schemeNormalizedCriticalDivisors k g) := by
  rw [normalized_postcriticalSet_eq_critical_orbit]
  have hUnion (S : ℕ → Set (SchemeDivisorPoint A)) :
      divisorSupport (⋃ n, S n) = ⋃ n, divisorSupport (S n) := by
    ext x
    simp only [divisorSupport, Set.mem_iUnion]
    constructor
    · rintro ⟨Q, ⟨n, hQ⟩, hx⟩
      exact ⟨n, Q, hQ, hx⟩
    · rintro ⟨n, Q, hQ, hx⟩
      exact ⟨Q, ⟨n, hQ⟩, hx⟩
  rw [hUnion]
  congr 1
  funext n
  exact (iterate_image_divisorSupport g
    (Pcf.coheight_apply_eq_one_of_finiteType g k)
    (schemeNormalizedCriticalDivisors k g) (n + 1)).symm

/-- The normalized branch support is contained in the postcritical support. -/
theorem normalized_branchSupport_subset_postcriticalSupport :
    divisorSupport (Pcf.schemeNormalizedBranch k g) ⊆
      divisorSupport (Pcf.schemeNormalizedPostcriticalSet k g) := by
  have hsubset : Pcf.schemeNormalizedBranch k g ⊆
      Pcf.schemeNormalizedPostcriticalSet k g := by
    intro Q hQ
    rw [Pcf.schemeNormalizedPostcriticalSet_eq_iUnion]
    exact Set.mem_iUnion.mpr ⟨0, by simpa using hQ⟩
  intro x hx
  simp only [divisorSupport, Set.mem_iUnion] at hx ⊢
  obtain ⟨Q, hQ, hx⟩ := hx
  exact ⟨Q, hsubset hQ, hx⟩

/-- PCF makes the actual union of postcritical divisors a closed subset. -/
theorem isClosed_normalized_postcriticalSupport
    (hpcf : Pcf.IsNormalizedPCF k g) :
    IsClosed (divisorSupport (Pcf.schemeNormalizedPostcriticalSet k g)) :=
  isClosed_divisorSupport _ hpcf

/-- The actual scheme map carries the union of postcritical divisors into itself. -/
theorem image_normalized_postcriticalSupport_subset :
    g '' divisorSupport (Pcf.schemeNormalizedPostcriticalSet k g) ⊆
      divisorSupport (Pcf.schemeNormalizedPostcriticalSet k g) := by
  have hstep :
      Pcf.schemeDivisorMap g (Pcf.coheight_apply_eq_one_of_finiteType g k) ''
        Pcf.schemeNormalizedPostcriticalSet k g ⊆
      Pcf.schemeNormalizedPostcriticalSet k g := by
    intro Q hQ
    rcases hQ with ⟨R, hR, rfl⟩
    rw [Pcf.schemeNormalizedPostcriticalSet_eq_iUnion] at hR ⊢
    rcases Set.mem_iUnion.mp hR with ⟨n, hn⟩
    refine Set.mem_iUnion.mpr ⟨n + 1, ?_⟩
    simpa only [Set.image_image, Function.iterate_succ_apply'] using
      (Set.mem_image_of_mem
        (Pcf.schemeDivisorMap g (Pcf.coheight_apply_eq_one_of_finiteType g k)) hn)
  rw [image_divisorSupport g (Pcf.coheight_apply_eq_one_of_finiteType g k)]
  intro x hx
  simp only [divisorSupport, Set.mem_iUnion] at hx ⊢
  obtain ⟨Q, hQ, hx⟩ := hx
  exact ⟨Q, hstep hQ, hx⟩

#check @normalized_branchSupport_subset_postcriticalSupport
#check @normalized_postcriticalSet_eq_critical_orbit
#check @normalized_postcriticalSupport_eq_critical_orbit
#check @isClosed_normalized_postcriticalSupport
#check @image_normalized_postcriticalSupport_subset
#print axioms normalized_postcriticalSet_eq_critical_orbit
#print axioms normalized_postcriticalSupport_eq_critical_orbit
#print axioms normalized_branchSupport_subset_postcriticalSupport
#print axioms isClosed_normalized_postcriticalSupport
#print axioms image_normalized_postcriticalSupport_subset

end Pcf.PaperCharZero
