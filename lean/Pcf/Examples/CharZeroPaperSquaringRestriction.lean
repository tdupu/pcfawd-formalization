/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingProjMapClosedImmersion
public import Pcf.PaperCharZero.SupportingClosureSubscheme
public import Pcf.Examples.CharZeroPaperSquaringBranch

/-!
# The restriction of projective squaring to `H_i`, `paper.tex`, `ex:squaring-PN`

Let `ψ` be coordinatewise squaring on `ℙ^N = Proj K[x_0, …, x_N]` and `H_i = V(x_i)`.
We construct the closed immersion `ι : ℙ^{N-1} → ℙ^N` onto `H_i` as `Proj` of the
surjective graded homomorphism setting `x_i = 0`, identify `ℙ^{N-1}` with the
reduced closure subscheme of `H_i`, and prove that under this identification the
actual restriction of `ψ` to `H_i` is coordinatewise squaring on `ℙ^{N-1}`.
-/

@[expose] public section
namespace Pcf.Examples.CharZeroPaperSquaringRestriction
open MvPolynomial AlgebraicGeometry CategoryTheory HomogeneousLocalization Pcf.PaperCharZero
open Pcf.Examples.CharZeroPaperSquaringProjective Pcf.Examples.CharZeroPaperSquaringBranch
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {m : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "gradeA" => MvPolynomial.homogeneousSubmodule (Fin (m + 1) ⊕ Unit) K
local notation "gradeB" => MvPolynomial.homogeneousSubmodule (Fin m ⊕ Unit) K
local notation "PolyA" => MvPolynomial (Fin (m + 1) ⊕ Unit) K
local notation "PolyB" => MvPolynomial (Fin m ⊕ Unit) K

/-! ## (a) Dropping one coordinate -/

/-- An equivalence of the coordinates of `ℙ^N` with `none` and the coordinates of
`ℙ^{N-1}`, sending `i` to `none`. -/
noncomputable def dropEquiv (i : Fin (m + 1) ⊕ Unit) :
    Fin (m + 1) ⊕ Unit ≃ Option (Fin m ⊕ Unit) :=
  let β : Fin (m + 1) ⊕ Unit ≃ Option (Fin m ⊕ Unit) := Fintype.equivOfCardEq (by simp)
  (Equiv.swap i (β.symm none)).trans β

@[simp] theorem dropEquiv_self (i : Fin (m + 1) ⊕ Unit) : dropEquiv i i = none := by
  simp [dropEquiv]

/-- The coordinate of `ℙ^N` corresponding to a coordinate of `ℙ^{N-1}`. -/
noncomputable def dropEmb (i : Fin (m + 1) ⊕ Unit) (k : Fin m ⊕ Unit) : Fin (m + 1) ⊕ Unit :=
  (dropEquiv i).symm (some k)

@[simp] theorem dropEquiv_dropEmb (i : Fin (m + 1) ⊕ Unit) (k : Fin m ⊕ Unit) :
    dropEquiv i (dropEmb i k) = some k := by
  simp [dropEmb]

/-! ## (b) The closed immersion -/

/-- The images of the coordinates: `x_i ↦ 0`, the others to the coordinates of
`ℙ^{N-1}`. -/
noncomputable def dropImage (i : Fin (m + 1) ⊕ Unit) (j : Fin (m + 1) ⊕ Unit) : PolyB :=
  (dropEquiv i j).elim 0 X

theorem dropImage_isHomogeneous (i j : Fin (m + 1) ⊕ Unit) :
    (dropImage (K := K) i j).IsHomogeneous 1 := by
  unfold dropImage
  cases dropEquiv i j with
  | none => exact isHomogeneous_zero _ _ _
  | some k => exact isHomogeneous_X K k

/-- The substitution `x_i ↦ 0`. -/
noncomputable def dropHom (i : Fin (m + 1) ⊕ Unit) : PolyA →ₐ[K] PolyB :=
  aeval (dropImage i)

@[simp] theorem dropHom_X (i j : Fin (m + 1) ⊕ Unit) :
    dropHom (K := K) i (X j) = dropImage i j := by
  simp [dropHom]

theorem dropHom_X_self (i : Fin (m + 1) ⊕ Unit) : dropHom (K := K) i (X i) = 0 := by
  simp [dropImage]

theorem dropHom_X_dropEmb (i : Fin (m + 1) ⊕ Unit) (k : Fin m ⊕ Unit) :
    dropHom (K := K) i (X (dropEmb i k)) = X k := by
  simp [dropImage]

theorem dropHom_mem (i : Fin (m + 1) ⊕ Unit) {d : ℕ} {P : PolyA} (hP : P ∈ gradeA d) :
    dropHom (K := K) i P ∈ gradeB d := by
  have h := (show P.IsHomogeneous d from hP).aeval (dropImage (K := K) i)
    (dropImage_isHomogeneous i)
  rw [one_mul] at h
  exact h

/-- The substitution as a graded ring homomorphism. -/
noncomputable def dropGradedHom (i : Fin (m + 1) ⊕ Unit) : gradeA →+*ᵍ gradeB where
  __ := (dropHom (K := K) i).toRingHom
  map_mem hx := dropHom_mem i hx

@[simp] theorem dropGradedHom_apply (i : Fin (m + 1) ⊕ Unit) (P : PolyA) :
    dropGradedHom (K := K) i P = dropHom i P := rfl

theorem dropHom_surjective (i : Fin (m + 1) ⊕ Unit) :
    Function.Surjective (dropHom (K := K) i) := by
  intro Q
  induction Q using MvPolynomial.induction_on with
  | C a => exact ⟨C a, by simp [dropHom]⟩
  | add P Q hP hQ =>
    obtain ⟨P', rfl⟩ := hP
    obtain ⟨Q', rfl⟩ := hQ
    exact ⟨P' + Q', map_add _ _ _⟩
  | mul_X P k hP =>
    obtain ⟨P', rfl⟩ := hP
    exact ⟨P' * X (dropEmb i k), by rw [map_mul, dropHom_X_dropEmb]⟩

theorem dropGradedHom_surjective (i : Fin (m + 1) ⊕ Unit) :
    Function.Surjective (dropGradedHom (K := K) i) :=
  dropHom_surjective i

/-- The closed immersion `ℙ^{N-1} → ℙ^N` onto `H_i`. -/
noncomputable def hyperplaneEmbedding (i : Fin (m + 1) ⊕ Unit) :
    AlgebraicGeometry.Proj gradeB ⟶ AlgebraicGeometry.Proj gradeA :=
  AlgebraicGeometry.Proj.map (dropGradedHom (K := K) i)
    (irrelevant_le_map_of_surjective _ (dropGradedHom_surjective i))

instance hyperplaneEmbedding_isClosedImmersion (i : Fin (m + 1) ⊕ Unit) :
    IsClosedImmersion (hyperplaneEmbedding (K := K) i) :=
  proj_map_isClosedImmersion _ _ (dropGradedHom_surjective i)
    (fun j : Fin (m + 1) ⊕ Unit => (X j : PolyA)) (fun _ => 1)
    (fun j => isHomogeneous_X K j) (fun _ => Nat.zero_lt_one)
    (projSourceCoordinates_basicOpen_cover (K := K) (n := m + 1))

/-! ## (c) The range is `V(x_i)` -/

/-- Setting `x_i = 0` and lifting back is the identity modulo `x_i`. -/
theorem sub_dropLift_mem (i : Fin (m + 1) ⊕ Unit) (P : PolyA) :
    P - aeval (fun k => (X (dropEmb i k) : PolyA)) (dropHom (K := K) i P) ∈
      Ideal.span {(X i : PolyA)} := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [dropHom]
  | add P Q hP hQ =>
    rw [map_add, map_add, add_sub_add_comm]
    exact Ideal.add_mem _ hP hQ
  | mul_X P j hP =>
    rw [map_mul, map_mul]
    have hj : (X j : PolyA) - aeval (fun k => (X (dropEmb i k) : PolyA))
        (dropHom (K := K) i (X j)) ∈ Ideal.span {(X i : PolyA)} := by
      rw [dropHom_X, dropImage]
      rcases h : dropEquiv i j with _ | k
      · have : j = i := (dropEquiv i).injective (h.trans (dropEquiv_self i).symm)
        subst this
        simp
      · have : dropEmb i k = j := by
          rw [dropEmb, ← h, Equiv.symm_apply_apply]
        simp [this]
    have : P * X j - aeval (fun k => (X (dropEmb i k) : PolyA)) (dropHom (K := K) i P) *
        aeval (fun k => (X (dropEmb i k) : PolyA)) (dropHom (K := K) i (X j)) =
      (P - aeval (fun k => (X (dropEmb i k) : PolyA)) (dropHom (K := K) i P)) * X j +
        aeval (fun k => (X (dropEmb i k) : PolyA)) (dropHom (K := K) i P) *
          (X j - aeval (fun k => (X (dropEmb i k) : PolyA)) (dropHom (K := K) i (X j))) := by
      ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hP) (Ideal.mul_mem_left _ _ hj)

/-- The kernel of the substitution is `(x_i)`. -/
theorem dropHom_ker (i : Fin (m + 1) ⊕ Unit) :
    RingHom.ker (dropHom (K := K) i).toRingHom = Ideal.span {(X i : PolyA)} := by
  apply le_antisymm
  · intro P hP
    have h := sub_dropLift_mem (K := K) i P
    rw [RingHom.mem_ker] at hP
    change dropHom i P = 0 at hP
    simpa [hP] using h
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    exact dropHom_X_self i

/-- The underlying point map of the embedding is contraction of homogeneous primes. -/
theorem hyperplaneEmbedding_apply_toIdeal (i : Fin (m + 1) ⊕ Unit)
    (q : AlgebraicGeometry.Proj gradeB) :
    ((hyperplaneEmbedding (K := K) i q : AlgebraicGeometry.Proj gradeA) :
        ProjectiveSpectrum gradeA).asHomogeneousIdeal.toIdeal =
      (q : ProjectiveSpectrum gradeB).asHomogeneousIdeal.toIdeal.comap
        (dropHom (K := K) i).toRingHom := rfl

/-- The generic point of `ℙ^{N-1}` maps to the generic point of `H_i`. -/
theorem hyperplaneEmbedding_genericPoint (i : Fin (m + 1) ⊕ Unit) :
    hyperplaneEmbedding (K := K) i (projGenericPoint (K := K) (n := m)) =
      hyperplane (K := K) (n := m + 1) i := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.toIdeal_injective
  rw [hyperplaneEmbedding_apply_toIdeal]
  change Ideal.comap _ ⊥ = Ideal.span {(X i : PolyA)}
  rw [← RingHom.ker_eq_comap_bot, dropHom_ker]

/-- `ex:squaring-PN`: the image of `ℙ^{N-1}` is exactly `V(x_i)`. -/
theorem hyperplaneEmbedding_range (i : Fin (m + 1) ⊕ Unit) :
    Set.range (hyperplaneEmbedding (K := K) i) =
      closure {(hyperplane (K := K) (n := m + 1) i : AlgebraicGeometry.Proj gradeA)} := by
  apply le_antisymm
  · rintro _ ⟨q, rfl⟩
    rw [hyperplane_closure, ProjectiveSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
    change X i ∈ ((hyperplaneEmbedding (K := K) i q : AlgebraicGeometry.Proj gradeA) :
        ProjectiveSpectrum gradeA).asHomogeneousIdeal.toIdeal
    rw [hyperplaneEmbedding_apply_toIdeal, Ideal.mem_comap]
    change dropHom (K := K) i (X i) ∈ _
    rw [dropHom_X_self]
    exact Ideal.zero_mem _
  · apply closure_minimal _ (hyperplaneEmbedding (K := K) i).isClosedEmbedding.isClosed_range
    rw [Set.singleton_subset_iff]
    exact ⟨_, hyperplaneEmbedding_genericPoint i⟩

/-- The identification of `ℙ^{N-1}` with the reduced closure subscheme of `H_i`. -/
noncomputable def hyperplaneSubschemeIso (i : Fin (m + 1) ⊕ Unit) :
    AlgebraicGeometry.Proj gradeB ≅
      (pointClosureIdealSheaf (hyperplane (K := K) (n := m + 1) i)).subscheme :=
  closureSubschemeIsoOfIsReduced (hyperplaneEmbedding i) _ (hyperplaneEmbedding_range i)

theorem hyperplaneSubschemeIso_hom_ι (i : Fin (m + 1) ⊕ Unit) :
    (hyperplaneSubschemeIso (K := K) i).hom ≫
        (pointClosureIdealSheaf (hyperplane (K := K) (n := m + 1) i)).subschemeι =
      hyperplaneEmbedding i :=
  closureSubschemeIsoOfIsReduced_hom_ι _ _ _

#print axioms dropEquiv_self
#print axioms dropHom_surjective
#print axioms hyperplaneEmbedding
#print axioms hyperplaneEmbedding_isClosedImmersion
#print axioms dropHom_ker
#print axioms hyperplaneEmbedding_genericPoint
#print axioms hyperplaneEmbedding_range
#print axioms hyperplaneSubschemeIso
#print axioms hyperplaneSubschemeIso_hom_ι
end Pcf.Examples.CharZeroPaperSquaringRestriction
