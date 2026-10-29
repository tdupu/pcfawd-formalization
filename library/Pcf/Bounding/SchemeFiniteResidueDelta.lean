/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeDeltaDynamics
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Finite residue extensions and weighted divisor degree -/

@[expose] public section

universe u v w

open AlgebraicGeometry CategoryTheory

namespace Pcf

set_option linter.style.haveILetI false

/-- The residue field extension at a point of a finite scheme morphism is finite. -/
theorem finiteResidueField_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    FiniteDimensional (Y.residueField (f x)) (X.residueField x) := by
  letI := (f.stalkMap x).hom.toAlgebra
  haveI : Algebra.QuasiFinite (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.quasiFiniteAt x)
  letI : Algebra (Y.presheaf.stalk (f x)) (X.residueField x) :=
    IsLocalRing.ResidueField.algebra _
  letI : Algebra (Y.presheaf.stalk (f x)) (Y.residueField (f x)) :=
    IsLocalRing.ResidueField.algebra _
  letI : Algebra (X.presheaf.stalk x) (X.residueField x) :=
    IsLocalRing.ResidueField.algebra _
  letI : IsScalarTower (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
      (X.residueField x) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.QuasiFinite (X.presheaf.stalk x) (X.residueField x) := by
    haveI : Module.Finite (X.presheaf.stalk x) (X.residueField x) :=
      Module.Finite.of_surjective
        (Algebra.linearMap (X.presheaf.stalk x) (X.residueField x))
        IsLocalRing.residue_surjective
    infer_instance
  letI : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have hq : Algebra.QuasiFinite (Y.presheaf.stalk (f x)) (X.residueField x) :=
    Algebra.QuasiFinite.trans _ (X.presheaf.stalk x) _
  letI : IsScalarTower (Y.presheaf.stalk (f x)) (Y.residueField (f x))
      (X.residueField x) := IsScalarTower.of_algebraMap_eq' (by
    change (IsLocalRing.residue (X.presheaf.stalk x)).comp (f.stalkMap x).hom =
      (IsLocalRing.ResidueField.map (f.stalkMap x).hom).comp
        (IsLocalRing.residue (Y.presheaf.stalk (f x)))
    exact (IsLocalRing.ResidueField.map_comp_residue (f.stalkMap x).hom).symm)
  haveI : Algebra.QuasiFinite (Y.residueField (f x)) (X.residueField x) :=
    Algebra.QuasiFinite.of_restrictScalars (Y.presheaf.stalk (f x)) _ _
  exact Module.Finite.of_quasiFinite

/-- Weighted divisor degree of a finite map is positive without a
separate residue-field finiteness premise. -/
theorem schemeDivisorDelta_pos_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] (d : SchemeDivisorPoint X) :
    0 < schemeDivisorDelta f d :=
  schemeDivisorDelta_pos f d (finiteResidueField_of_isFinite f d.1)

/-- The weighted degree tower law for finite scheme morphisms, with
the intermediate residue-field algebraicity obtained from finiteness.

`paper-p.tex` correspondence: Lemma 5.2 (`lem:tower`). -/
theorem schemeDivisorDelta_comp_of_isFinite
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [IsDominant f] [IsFinite g]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormalScheme Y]
    (d : SchemeDivisorPoint X) :
    schemeDivisorDelta (f ≫ g) d =
      schemeDivisorDelta g (d.mapFiniteDominantNormal f) *
        schemeDivisorDelta f d := by
  apply schemeDivisorDelta_comp f g d
  letI := (g.residueFieldMap (f d.1)).hom.toAlgebra
  letI : FiniteDimensional (Z.residueField (g (f d.1)))
      (Y.residueField (f d.1)) := finiteResidueField_of_isFinite g (f d.1)
  infer_instance

/-- `paper-p.tex`, Lemma `lem:tower`, displayed local-degree composition
formula in the manuscript's factor order. Apply this to the finite lifts
between normalizations.

`paper-p.tex` correspondence: Lemma 5.2 (`lem:tower`). -/
theorem paperP_localDegree_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [IsDominant f] [IsFinite g]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormalScheme Y]
    (d : SchemeDivisorPoint X) :
    schemeDivisorDelta (f ≫ g) d =
      schemeDivisorDelta f d *
        schemeDivisorDelta g (d.mapFiniteDominantNormal f) := by
  rw [schemeDivisorDelta_comp_of_isFinite f g d, Nat.mul_comm]

/-- The weighted local-degree identity in an actual commuting square of
finite dominant normal scheme maps now has no residue-field hypotheses. -/
theorem schemeDeltaDynamics_comparison_tower_of_isFinite
    {X Y : Scheme.{u}} (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsFinite π] [IsDominant π]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    (hcomm : g ≫ π = π ≫ f) (d : SchemeDivisorPoint Y) :
    schemeDivisorDelta f (d.mapFiniteDominantNormal π) * schemeDivisorDelta π d =
      schemeDivisorDelta π (d.mapFiniteDominantNormal g) * schemeDivisorDelta g d := by
  have hleft := schemeDivisorDelta_comp_of_isFinite π f d
  have hright := schemeDivisorDelta_comp_of_isFinite g π d
  rw [hcomm] at hright
  exact hleft.symm.trans hright

/-- Scheme-level PCF descent for a finite comparison square: residue
extensions, local-degree positivity, divisor surjectivity, finite fibers,
and the weighted tower law follow from finite morphisms. Only finiteness
of the weighted branch and comparison critical sets remains explicit. -/
theorem schemeDeltaDynamics_isPCF_of_separable_comparison_of_isFinite
    {X Y : Scheme.{u}} (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsFinite π] [IsDominant π]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    (hcomm : g ≫ π = π ≫ f)
    (hDbranch : (schemeDeltaDynamicsOfFiniteDominantNormal f).branch.Finite)
    (hπcritical : {d : SchemeDivisorPoint Y | 1 < schemeDivisorDelta π d}.Finite)
    (hE : (schemeDeltaDynamicsOfFiniteDominantNormal g).IsPCF) :
    (schemeDeltaDynamicsOfFiniteDominantNormal f).IsPCF := by
  apply schemeDeltaDynamics_isPCF_of_separable_comparison f g π hcomm
  · intro d
    letI := (f.residueFieldMap (π d.1)).hom.toAlgebra
    letI : FiniteDimensional (X.residueField (f (π d.1)))
        (X.residueField (π d.1)) := finiteResidueField_of_isFinite f (π d.1)
    infer_instance
  · intro d
    letI := (π.residueFieldMap (g d.1)).hom.toAlgebra
    letI : FiniteDimensional (X.residueField (π (g d.1)))
        (Y.residueField (g d.1)) := finiteResidueField_of_isFinite π (g d.1)
    infer_instance
  · exact schemeDivisorDelta_pos_of_isFinite f
  · exact schemeDivisorDelta_pos_of_isFinite g
  · exact schemeDivisorDelta_pos_of_isFinite π
  · exact hDbranch
  · exact hπcritical
  · exact hE

private theorem one_lt_mul_iff_of_pos (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    1 < a * b ↔ 1 < a ∨ 1 < b := by
  constructor
  · intro h
    by_contra hn
    have ⟨_hna, _hnb⟩ := not_or.mp hn
    have ha1 : a = 1 := by omega
    have hb1 : b = 1 := by omega
    simp [ha1, hb1] at h
  · intro h
    rcases h with h | h <;> nlinarith

private theorem weighted_branch_comp
    {P : Type u} {Q : Type v} {R : Type w}
    (f : P → Q) (g : Q → R) (δf : P → ℕ) (δg : Q → ℕ)
    (hsurj : Function.Surjective f)
    (hposf : ∀ p, 0 < δf p) (hposg : ∀ q, 0 < δg q) :
    {r | ∃ p, g (f p) = r ∧ 1 < δg (f p) * δf p} =
      {r | ∃ q, g q = r ∧ 1 < δg q} ∪
        g '' {q | ∃ p, f p = q ∧ 1 < δf p} := by
  ext r
  constructor
  · rintro ⟨p, rfl, hp⟩
    rcases ((one_lt_mul_iff_of_pos _ _ (hposg (f p)) (hposf p)).mp hp) with h | h
    · exact Or.inl ⟨f p, rfl, h⟩
    · exact Or.inr ⟨f p, ⟨p, rfl, h⟩, rfl⟩
  · rintro (⟨q, rfl, hq⟩ | ⟨q, ⟨p, rfl, hp⟩, rfl⟩)
    · obtain ⟨p, rfl⟩ := hsurj q
      exact ⟨p, rfl, (one_lt_mul_iff_of_pos _ _ (hposg (f p)) (hposf p)).mpr (Or.inl hq)⟩
    · exact ⟨p, rfl, (one_lt_mul_iff_of_pos _ _ (hposg (f p)) (hposf p)).mpr (Or.inr hp)⟩

/-- The weighted branch-divisor tower identity of `paper-p.tex`, Lemma
`lem:tower`, for actual finite dominant maps of normal schemes. The weight
is the ramification index times the inseparable residue degree.

`paper-p.tex` correspondence: Lemma 5.2 (`lem:tower`). -/
theorem schemeDelta_branch_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    [IsNormalScheme Y] [IsNormalScheme Z] :
    {r : SchemeDivisorPoint Z | ∃ p : SchemeDivisorPoint X,
      p.mapFiniteDominantNormal (f ≫ g) = r ∧
        1 < schemeDivisorDelta (f ≫ g) p} =
      {r : SchemeDivisorPoint Z | ∃ q : SchemeDivisorPoint Y,
        q.mapFiniteDominantNormal g = r ∧ 1 < schemeDivisorDelta g q} ∪
      (fun q : SchemeDivisorPoint Y => q.mapFiniteDominantNormal g) ''
        {q : SchemeDivisorPoint Y | ∃ p : SchemeDivisorPoint X,
          p.mapFiniteDominantNormal f = q ∧ 1 < schemeDivisorDelta f p} := by
  have hcomp (p : SchemeDivisorPoint X) :
      p.mapFiniteDominantNormal (f ≫ g) =
        (p.mapFiniteDominantNormal f).mapFiniteDominantNormal g := by
    apply Subtype.ext
    rfl
  let F : SchemeDivisorPoint X → SchemeDivisorPoint Y :=
    fun p => p.mapFiniteDominantNormal f
  let G : SchemeDivisorPoint Y → SchemeDivisorPoint Z :=
    fun q => q.mapFiniteDominantNormal g
  have h := weighted_branch_comp F G (schemeDivisorDelta f) (schemeDivisorDelta g)
    (SchemeDivisorPoint.mapFiniteDominantNormal_surjective f)
    (schemeDivisorDelta_pos_of_isFinite f)
    (schemeDivisorDelta_pos_of_isFinite g)
  convert h using 1
  ext r
  simp only [Set.mem_ofPred_eq, hcomp]
  constructor
  · rintro ⟨p, hp, hδ⟩
    exact ⟨p, hp, by simpa only [schemeDivisorDelta_comp_of_isFinite] using hδ⟩
  · rintro ⟨p, hp, hδ⟩
    exact ⟨p, hp, by simpa only [schemeDivisorDelta_comp_of_isFinite] using hδ⟩

#print axioms schemeDelta_branch_comp
#print axioms finiteResidueField_of_isFinite
#print axioms schemeDivisorDelta_pos_of_isFinite
#print axioms schemeDivisorDelta_comp_of_isFinite
#print axioms paperP_localDegree_comp
#print axioms schemeDeltaDynamics_comparison_tower_of_isFinite
#print axioms schemeDeltaDynamics_isPCF_of_separable_comparison_of_isFinite

end Pcf
