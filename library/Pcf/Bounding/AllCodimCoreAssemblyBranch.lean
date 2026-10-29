/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimCoreDefs

/-!
# Branch divisors of iterates lie over the postcritical set

For a finite dominant generically separable self-map `g` of a normal integral
locally Noetherian scheme, every divisor at which an iterate `g^N` fails to be
formally étale is sent by `g^N` into the non-étale postcritical set of `g`.
This supplies the uniform branch hypothesis `B` of `AllCodimAffineCore` for
all iterates at once, as in `latex/paper-p.tex`, proof of Theorem
`thm:allcodim-normal`.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- An isomorphism of commutative rings is formally étale. -/
theorem commRingCat_hom_formallyEtale_of_isIso {A B : CommRingCat.{u}} (φ : A ⟶ B)
    [IsIso φ] : φ.hom.FormallyEtale := by
  letI := φ.hom.toAlgebra
  change Algebra.FormallyEtale A B
  exact Algebra.FormallyEtale.of_equiv
    (AlgEquiv.ofBijective (Algebra.ofId A B) (ConcreteCategory.bijective_of_isIso φ))

/-- If `g` is formally étale along the first `N` points of an orbit, then so
is `g^N` at the starting point. -/
theorem stalkMap_end_pow_formallyEtale {Y : Scheme.{u}} (g : Y ⟶ Y) (N : ℕ) (x : Y)
    (h : ∀ i < N, (g.stalkMap ((End.of g ^ i).asHom.base x)).hom.FormallyEtale) :
    ((End.of g ^ N).asHom.stalkMap x).hom.FormallyEtale := by
  induction N generalizing x with
  | zero =>
      change ((𝟙 Y : Y ⟶ Y).stalkMap x).hom.FormallyEtale
      exact commRingCat_hom_formallyEtale_of_isIso _
  | succ N ih =>
      have hih := ih (g x) (fun i hi => by
        have := h (i + 1) (by omega)
        rw [pow_succ] at this
        exact this)
      have h0 := h 0 (by omega)
      rw [pow_succ]
      change ((g ≫ (End.of g ^ N).asHom).stalkMap x).hom.FormallyEtale
      have h0' : (g.stalkMap x).hom.FormallyEtale := h0
      rw [Scheme.Hom.stalkMap_comp]
      exact RingHom.FormallyEtale.comp hih h0'

variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormalScheme Y]
  [NoetherianSpace Y] (g : Y ⟶ Y) [IsFinite g] [IsDominant g]
  (hsep : IsGenericallySeparable g)

/-- Iterating the divisor dynamics moves the point by the scheme iterate. -/
theorem unnormalizedDynamics_iterate_val (i : ℕ) (w : SchemeDivisorPoint Y) :
    ((unnormalizedDynamicsOfFiniteDominantNormalSeparable g hsep).step^[i] w).1 =
      (End.of g ^ i).asHom.base w.1 := by
  induction i generalizing w with
  | zero => rfl
  | succ i ih =>
      rw [Function.iterate_succ_apply, ih, pow_succ]
      rfl

/-- **Branch divisors of iterates lie over the postcritical set.** -/
theorem formallyEtale_end_pow_of_notMem_postcritical (N : ℕ) (w : SchemeDivisorPoint Y)
    (hw : (End.of g ^ N).asHom.base w.1 ∉ Subtype.val ''
      (unnormalizedDynamicsOfFiniteDominantNormalSeparable g hsep).nonEtalePostcriticalSet) :
    ((End.of g ^ N).asHom.stalkMap w.1).hom.FormallyEtale := by
  let D := unnormalizedDynamicsOfFiniteDominantNormalSeparable g hsep
  apply stalkMap_end_pow_formallyEtale g N w.1
  intro i hi
  by_contra hne
  apply hw
  let wi := D.step^[i] w
  have hwi : wi.1 = (End.of g ^ i).asHom.base w.1 := unnormalizedDynamics_iterate_val g hsep i w
  have hloc : wi ∈ D.nonEtaleLocus 1 := by
    change ¬ (((End.of g ^ 1).asHom).stalkMap wi.1).hom.FormallyEtale
    rw [pow_one, hwi]
    exact hne
  refine ⟨D.step^[N] w, ?_, unnormalizedDynamics_iterate_val g hsep N w⟩
  refine (D.mem_nonEtalePostcriticalSet_iff).mpr
    ⟨N - (i + 1), D.step^[1] wi, ⟨wi, hloc, rfl⟩, ?_⟩
  change D.step^[N - (i + 1)] (D.step^[1] (D.step^[i] w)) = D.step^[N] w
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
  congr 1
  omega

#print axioms stalkMap_end_pow_formallyEtale
#print axioms formallyEtale_end_pow_of_notMem_postcritical

end
end Pcf
