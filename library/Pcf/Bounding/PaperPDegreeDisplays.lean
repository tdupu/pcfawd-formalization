/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeGenericSeparabilityMap
public import Pcf.Bounding.SchemePrimaryNormalizationDeltaDegree

/-!
# Degree displays in the proof of `lem:pcf-transfer-charp`

* Display l. 1913: for a finite commuting square `π h = g π` of dominant
  maps of integral schemes, multiplicativity of inseparable degrees in the
  two function-field towers gives `[h]_insep [π]_insep = [π]_insep [g]_insep`.
  Here `[φ]_insep` is the finite inseparable degree of the actual
  rational-function pullback `schemeGenericFieldHom φ`.
* Display l. 1969: for the normalization `ρ` of a normal integral scheme `M`
  in a finite purely inseparable extension `E` of its function field, and a
  divisor `D` upstairs with image `D_M`, the residue extension is purely
  inseparable and `q = e(D/D_M) [κ(D):κ(D_M)]` with `q = [E : k(M)]`; hence
  `δ_ρ(D) = q`.

In the source, `ρ : Y' → M` is the second factor of `π = σ ρ` with `Y'`
normal; the identification of that `ρ` with the normalization of `M` in
`E = k(Y')` is not formalized here (see the evidence file).
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- Multiplicativity of finite inseparable degrees along a composite of
field homomorphisms, with the algebra structures given by the maps. -/
theorem finInsepDegree_comp_ringHom {K L M : Type*} [Field K] [Field L] [Field M]
    (a : K →+* L) (b : L →+* M)
    (ha : letI := a.toAlgebra; FiniteDimensional K L) :
    @Field.finInsepDegree K M _ _ (b.comp a).toAlgebra =
      @Field.finInsepDegree K L _ _ a.toAlgebra *
        @Field.finInsepDegree L M _ _ b.toAlgebra := by
  letI : Algebra K L := a.toAlgebra
  letI : Algebra L M := b.toAlgebra
  letI : Algebra K M := (b.comp a).toAlgebra
  letI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional K L := ha
  exact (Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic K L M).symm

/-- The inseparable degree `[φ]_insep` of the function-field extension of a
dominant morphism of integral schemes, computed on the actual
rational-function pullback. -/
noncomputable def schemeGenericInsepDegree
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (φ : Y ⟶ X) [IsDominant φ] : ℕ :=
  @Field.finInsepDegree X.functionField Y.functionField _ _
    (schemeGenericFieldHom φ).toAlgebra

/-- **Display l. 1913** (`lem:pcf-transfer-charp`). For finite dominant maps
`f : X → X`, `g : Y → Y`, `π : Y → X` of integral schemes with
`g ≫ π = π ≫ f` (the source's `π h = g π`, with source `h` = Lean `g` and
source `g` = Lean `f`), `[g]_insep [π]_insep = [π]_insep [f]_insep`. -/
theorem schemeGenericInsepDegree_commuting_square
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsFinite g] [IsFinite π]
    [IsDominant f] [IsDominant g] [IsDominant π]
    (hcomm : g ≫ π = π ≫ f) :
    schemeGenericInsepDegree g * schemeGenericInsepDegree π =
      schemeGenericInsepDegree π * schemeGenericInsepDegree f := by
  have h1 := finInsepDegree_comp_ringHom (schemeGenericFieldHom π)
    (schemeGenericFieldHom g) (schemeGenericFieldHom_finite π)
  have h2 := finInsepDegree_comp_ringHom (schemeGenericFieldHom f)
    (schemeGenericFieldHom π) (schemeGenericFieldHom_finite f)
  rw [schemeGenericFieldHom_commuting_square f g π hcomm] at h1
  unfold schemeGenericInsepDegree
  rw [mul_comm, ← h1, h2]
  exact Nat.mul_comm _ _

/-- **Display l. 1969** (`lem:pcf-transfer-charp`). Let `ρ` be the
normalization of a normal integral scheme `M` (Lean `X`) in a finite purely
inseparable extension `E` (Lean `L`) of its function field, and
`q = [E : k(M)]`. For every integral effective divisor `D` upstairs, with
`D_M = ρ(D)`: the residue extension `κ(D)/κ(D_M)` is purely inseparable,
`q = e(D/D_M) [κ(D):κ(D_M)]`, and hence `δ_ρ(D) = q`. -/
theorem paperP_transfer_purelyInseparable_degree_display
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L]
    [IsPurelyInseparable X.functionField L]
    [IsFinite (schemeFieldExtensionInclusion X L).fromNormalization]
    [IsDominant (schemeFieldExtensionInclusion X L).fromNormalization]
    [IsIntegral (schemeFieldExtensionInclusion X L).normalization]
    (U : X.affineOpens) [Nonempty (U : X.Opens)]
    (d : SchemeDivisorPoint (schemeFieldExtensionInclusion X L).normalization)
    (hd : d.1 ∈ (schemeFieldExtensionInclusion X L).fromNormalization ⁻¹ᵁ
      (U : X.Opens))
    (pchar : ℕ) [ExpChar X.functionField pchar]
    [ExpChar ((U.2.primeIdealOf
      ⟨(schemeFieldExtensionInclusion X L).fromNormalization d.1, hd⟩).asIdeal).ResidueField
      pchar] :
    letI : Algebra
      (X.residueField ((schemeFieldExtensionInclusion X L).fromNormalization d.1))
      ((schemeFieldExtensionInclusion X L).normalization.residueField d.1) :=
      ((schemeFieldExtensionInclusion X L).fromNormalization.residueFieldMap d.1).hom.toAlgebra
    IsPurelyInseparable
        (X.residueField ((schemeFieldExtensionInclusion X L).fromNormalization d.1))
        ((schemeFieldExtensionInclusion X L).normalization.residueField d.1) ∧
      Module.finrank X.functionField L =
        schemeDivisorRamificationIdx (schemeFieldExtensionInclusion X L).fromNormalization d *
          Module.finrank
            (X.residueField ((schemeFieldExtensionInclusion X L).fromNormalization d.1))
            ((schemeFieldExtensionInclusion X L).normalization.residueField d.1) ∧
      schemeDivisorDelta (schemeFieldExtensionInclusion X L).fromNormalization d =
        Module.finrank X.functionField L := by
  letI : Algebra
      (X.residueField ((schemeFieldExtensionInclusion X L).fromNormalization d.1))
      ((schemeFieldExtensionInclusion X L).normalization.residueField d.1) :=
    ((schemeFieldExtensionInclusion X L).fromNormalization.residueFieldMap d.1).hom.toAlgebra
  have hpure := schemeFieldExtensionNormalization_residueField_isPurelyInseparable
    X L U d.1 hd pchar
  have hδ := schemeFieldExtensionNormalization_divisorDelta_eq_genericDegree
    X L U d hd pchar
  refine ⟨hpure, ?_, hδ⟩
  rw [← hδ]
  unfold schemeDivisorDelta
  rw [IsPurelyInseparable.finInsepDegree_eq]

#print axioms finInsepDegree_comp_ringHom
#print axioms schemeGenericInsepDegree_commuting_square
#print axioms paperP_transfer_purelyInseparable_degree_display

end

end Pcf
