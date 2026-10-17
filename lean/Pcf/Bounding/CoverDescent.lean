/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeDynamics

/-!
# PCF descent through ramified finite covers

The argument of `lem:covers` in `latex/paper.tex` bounds the downstairs
postcritical set by `π '' PC(g) ∪ Branch(π)`.  The first theorem isolates exactly
the one-step branch inclusion needed for this argument; it does not assume an
orbit bound or the PCF conclusion.

`DivisorDynamics.RamifiedCover` records positive ramification indices for the cover,
finite fibres, surjectivity, the commuting square, and multiplicativity of
ramification around that square.  The branch identity is proved from these
data, rather than supplied as a field.  The scheme constructor obtains this
multiplicativity from the actual stalk theorem `schemeDivisorRam_comp`.

The scheme statements below concern normal integral schemes.  Applying them
to nonnormal varieties additionally requires passage to the normalizations
and comparison with the manuscript's normalized branch locus.
-/

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf
namespace DivisorDynamics

variable {P : Type u} {Q : Type v} (D : DivisorDynamics P) (E : DivisorDynamics Q)

/-- The finite invariant set in the proof of `lem:covers`. -/
def ramifiedCoverBound (π : Q → P) (C : Set P) : Set P := π '' E.postcriticalSet ∪ C

/-- The one-step branch inclusion and semiconjugacy imply the manuscript's
postcritical-set bound.  Finite fibres are unnecessary in this direction. -/
theorem pcSet_subset_ramifiedCoverBound (π : Q → P) (C : Set P)
    (hcomm : ∀ q, π (E.step q) = D.step (π q))
    (hbranch : D.branch ∪ D.step '' C ⊆ C ∪ π '' E.branch) :
    D.postcriticalSet ⊆ E.ramifiedCoverBound π C := by
  have hinit : D.branch ⊆ E.ramifiedCoverBound π C := by
    intro p hp
    rcases hbranch (Or.inl hp) with hpC | ⟨q, hq, rfl⟩
    · exact Or.inr hpC
    · exact Or.inl ⟨q, E.branch_subset_postcriticalSet hq, rfl⟩
  have hstep : ∀ p ∈ E.ramifiedCoverBound π C,
      D.step p ∈ E.ramifiedCoverBound π C := by
    rintro p (⟨q, hq, rfl⟩ | hpC)
    · exact Or.inl ⟨E.step q, E.step_image_postcriticalSet_subset ⟨q, hq, rfl⟩, hcomm q⟩
    · rcases hbranch (Or.inr ⟨p, hpC, rfl⟩) with hpC' | ⟨q, hq, hqp⟩
      · exact Or.inr hpC'
      · exact Or.inl ⟨q, E.branch_subset_postcriticalSet hq, hqp⟩
  intro p hp
  obtain ⟨n, q, hq, rfl⟩ := D.mem_postcriticalSet_iff.mp hp
  clear hp
  induction n with
  | zero => exact hinit hq
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hstep _ ih

/-- Set-theoretic form of `lem:covers`, with its minimal branch input visible. -/
theorem pcf_of_ramified_branch_union (π : Q → P) (C : Set P)
    (hcomm : ∀ q, π (E.step q) = D.step (π q)) (hC : C.Finite)
    (hbranch : D.branch ∪ D.step '' C ⊆ C ∪ π '' E.branch)
    (hE : E.IsPCF) : D.IsPCF :=
  ((hE.image π).union hC).subset
    (D.pcSet_subset_ramifiedCoverBound E π C hcomm hbranch)

/-- Divisor data of a finite ramified cover intertwining two self-maps.
`ram_comp` is the equality of the two ramification products in the commuting
square; it is a local identity, independent of PCF. -/
structure RamifiedCover where
  /-- Pushforward through the cover. -/
  map : Q → P
  /-- Every downstairs divisor lifts. -/
  map_surjective : Function.Surjective map
  /-- Only finitely many divisors lie over a fixed divisor. -/
  finite_fiber : ∀ p, (map ⁻¹' {p}).Finite
  /-- The cover intertwines the self-maps. -/
  comm : ∀ q, map (E.step q) = D.step (map q)
  /-- Ramification index of the cover. -/
  ram : Q → ℕ
  /-- The indices are positive. -/
  ram_pos : ∀ q, 0 < ram q
  /-- The cover has finitely many branch divisors. -/
  branch_finite : {p | ∃ q, map q = p ∧ 1 < ram q}.Finite
  /-- Multiplicativity around the commuting square. -/
  ram_comp : ∀ q, D.ramificationIdx (map q) * ram q = ram (E.step q) * E.ramificationIdx q

namespace RamifiedCover

variable {D E} (C : RamifiedCover D E)

/-- Branch divisors of the cover itself. -/
def branch : Set P := {p | ∃ q, C.map q = p ∧ 1 < C.ram q}

/-- Finiteness of a divisor set is preserved by inverse image through the
cover. This records the geometric finite-fibre input separately from descent. -/
theorem finite_preimage {S : Set P} (hS : S.Finite) : (C.map ⁻¹' S).Finite :=
  hS.preimage' fun p _ ↦ C.finite_fiber p

private theorem one_lt_mul_iff_of_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    1 < a * b ↔ 1 < a ∨ 1 < b := by
  constructor
  · intro h
    by_contra hn
    have ha' : a = 1 := by omega
    have hb' : b = 1 := by omega
    simp [ha', hb'] at h
  · rintro (ha' | hb')
    · exact ha'.trans_le (Nat.le_mul_of_pos_right _ hb)
    · exact hb'.trans_le (Nat.le_mul_of_pos_left _ ha)

/-- The tower formula on both sides of the commuting square gives the exact
branch identity used in `lem:covers`. -/
theorem branch_union :
    D.branch ∪ D.step '' C.branch = C.branch ∪ C.map '' E.branch := by
  have hram (q : Q) :
      (1 < D.ramificationIdx (C.map q) ∨ 1 < C.ram q) ↔
        (1 < C.ram (E.step q) ∨ 1 < E.ramificationIdx q) := by
    rw [← one_lt_mul_iff_of_pos (D.ramificationIdx_pos _) (C.ram_pos _), C.ram_comp,
      one_lt_mul_iff_of_pos (C.ram_pos _) (E.ramificationIdx_pos _)]
  apply Set.Subset.antisymm
  · rintro p (hp | ⟨r, hr, rfl⟩)
    · obtain ⟨r, hr, hrRam⟩ := hp
      obtain ⟨q, hq⟩ := C.map_surjective r
      have hqp : C.map (E.step q) = p := by rw [C.comm, hq, hr]
      rcases (hram q).mp (Or.inl (hq ▸ hrRam)) with h | h
      · exact Or.inl ⟨E.step q, hqp, h⟩
      · exact Or.inr ⟨E.step q, ⟨q, rfl, h⟩, hqp⟩
    · obtain ⟨q, rfl, hq⟩ := hr
      rcases (hram q).mp (Or.inr hq) with h | h
      · exact Or.inl ⟨E.step q, C.comm q, h⟩
      · exact Or.inr ⟨E.step q, ⟨q, rfl, h⟩, C.comm q⟩
  · rintro p (hp | ⟨r, hr, rfl⟩)
    · obtain ⟨r, hr, hrRam⟩ := hp
      obtain ⟨q, hq⟩ := E.step_surjective r
      have hqp : D.step (C.map q) = p := by rw [← C.comm, hq, hr]
      rcases (hram q).mpr (Or.inl (hq ▸ hrRam)) with h | h
      · exact Or.inl ⟨C.map q, hqp, h⟩
      · exact Or.inr ⟨C.map q, ⟨q, rfl, h⟩, hqp⟩
    · obtain ⟨q, rfl, hq⟩ := hr
      rcases (hram q).mpr (Or.inr hq) with h | h
      · exact Or.inl ⟨C.map q, (C.comm q).symm, h⟩
      · exact Or.inr ⟨C.map q, ⟨q, rfl, h⟩, (C.comm q).symm⟩

/-- Every downstairs postcritical divisor lies in the image of the upstairs
postcritical set or in the branch locus of the cover. -/
theorem pcSet_subset : D.postcriticalSet ⊆ E.ramifiedCoverBound C.map C.branch :=
  D.pcSet_subset_ramifiedCoverBound E C.map C.branch C.comm C.branch_union.le

include C in
/-- PCF descends through a ramified cover. -/
theorem pcf (hE : E.IsPCF) : D.IsPCF :=
  D.pcf_of_ramified_branch_union E C.map C.branch C.comm C.branch_finite
    C.branch_union.le hE

end RamifiedCover
end DivisorDynamics

set_option linter.style.haveILetI false

/-- The actual divisor cover between normal integral schemes. All map and
ramification fields come from the given scheme morphisms. -/
noncomputable def schemeRamifiedCover
    {X Y : Scheme.{u}} (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsFinite π] [IsDominant π]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormalScheme Y]
    (hf : (schemeDivisorCrit1 f).Finite) (hg : (schemeDivisorCrit1 g).Finite)
    (hπ : (schemeDivisorCrit1 π).Finite) (hcomm : g ≫ π = π ≫ f) :
    DivisorDynamics.RamifiedCover (divDynOfFiniteDominantNormal f hf)
      (divDynOfFiniteDominantNormal g hg) where
  map q := q.mapFiniteDominantNormal π
  map_surjective := SchemeDivisorPoint.mapFiniteDominantNormal_surjective π
  finite_fiber := SchemeDivisorPoint.mapFiniteDominantNormal_finite_fiber π
  comm q := by
    apply Subtype.ext
    change π (g q.1) = f (π q.1)
    simpa only [AlgebraicGeometry.Scheme.Hom.comp_apply] using
      congrArg (fun h : Y ⟶ X ↦ h q.1) hcomm
  ram := schemeDivisorRam π
  ram_pos := schemeDivisorRam_pos π
  branch_finite := by
    refine (hπ.image (fun q ↦ q.mapFiniteDominantNormal π)).subset ?_
    rintro p ⟨q, hqp, hq⟩
    exact ⟨q, schemeDivisorRam_gt_one_mem_crit1 π q hq, hqp⟩
  ram_comp q := by
    change schemeDivisorRam f (q.mapFiniteDominantNormal π) * schemeDivisorRam π q =
      schemeDivisorRam π (q.mapFiniteDominantNormal g) * schemeDivisorRam g q
    rw [← schemeDivisorRam_comp π f, ← schemeDivisorRam_comp g π, hcomm]

/-- Scheme-level `lem:covers` for normal schemes, with the finiteness of the
three actual critical divisor loci explicitly supplied. -/
theorem scheme_pcf_of_ramified_cover
    {X Y : Scheme.{u}} (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsFinite π] [IsDominant π]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormalScheme Y]
    (hf : (schemeDivisorCrit1 f).Finite) (hg : (schemeDivisorCrit1 g).Finite)
    (hπ : (schemeDivisorCrit1 π).Finite) (hcomm : g ≫ π = π ≫ f)
    (hpcf : (divDynOfFiniteDominantNormal g hg).IsPCF) :
    (divDynOfFiniteDominantNormal f hf).IsPCF :=
  (schemeRamifiedCover f g π hf hg hπ hcomm).pcf hpcf

/-- A finite dominant cover of integral schemes is formally étale at the
generic point when the target function field has characteristic zero. -/
theorem formallyEtale_stalkMap_genericPoint_of_cover_charZero
    {X Y : Scheme.{u}} (π : Y ⟶ X) [IsFinite π] [IsDominant π]
    [IsIntegral X] [IsIntegral Y]
    [CharZero (X.presheaf.stalk (genericPoint X))] :
    (π.stalkMap (genericPoint Y)).hom.FormallyEtale := by
  have hgp : π (genericPoint Y) = genericPoint X :=
    map_genericPoint_eq_of_isDominant π
  let e := (X.presheaf.stalkCongr (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  have hfield : IsField (X.presheaf.stalk (π (genericPoint Y))) :=
    e.toMulEquiv.isField (Field.toIsField _)
  letI : Field (X.presheaf.stalk (π (genericPoint Y))) := hfield.toField
  letI : CharZero (X.presheaf.stalk (π (genericPoint Y))) :=
    charZero_of_injective_ringHom e.symm.injective
  letI := (π.stalkMap (genericPoint Y)).hom.toAlgebra
  letI : FaithfulSMul (X.presheaf.stalk (π (genericPoint Y)))
      (Y.presheaf.stalk (genericPoint Y)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (π.stalkMap (genericPoint Y)).hom.injective
  letI : Algebra.QuasiFinite (X.presheaf.stalk (π (genericPoint Y)))
      (Y.presheaf.stalk (genericPoint Y)) := π.quasiFiniteAt (genericPoint Y)
  letI : Module.Finite (X.presheaf.stalk (π (genericPoint Y)))
      (Y.presheaf.stalk (genericPoint Y)) :=
    Algebra.QuasiFinite.iff_of_isArtinianRing.mp inferInstance
  letI : PerfectField (X.presheaf.stalk (π (genericPoint Y))) :=
    PerfectField.ofCharZero
  rw [RingHom.FormallyEtale]
  exact Algebra.FormallyEtale.of_isSeparable
    (X.presheaf.stalk (π (genericPoint Y))) (Y.presheaf.stalk (genericPoint Y))

/-- Finite dominant covers in characteristic zero have finitely many critical
divisor points on a Noetherian integral source. -/
theorem schemeDivisorCrit1_finite_of_cover_charZero
    {X Y : Scheme.{u}} (π : Y ⟶ X) [IsFinite π] [IsDominant π]
    [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [NoetherianSpace Y]
    [CharZero (X.presheaf.stalk (genericPoint X))] :
    (schemeDivisorCrit1 π).Finite :=
  schemeDivisorCrit1_finite_of_exists_formallyEtale π
    ⟨genericPoint Y, formallyEtale_stalkMap_genericPoint_of_cover_charZero π⟩

/-- The actual ramified divisor cover of Noetherian normal integral schemes
in characteristic zero. No branch-finiteness or tower identity is assumed. -/
noncomputable def schemeRamifiedCoverCharZero
    {X Y : Scheme.{u}} (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsFinite π] [IsDominant π]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X] [NoetherianSpace X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormalScheme Y] [NoetherianSpace Y]
    [CharZero (X.presheaf.stalk (genericPoint X))]
    [CharZero (Y.presheaf.stalk (genericPoint Y))]
    (hcomm : g ≫ π = π ≫ f) :
    DivisorDynamics.RamifiedCover (divDynOfFiniteDominantNormalCharZero f)
      (divDynOfFiniteDominantNormalCharZero g) :=
  schemeRamifiedCover f g π
    (schemeDivisorCrit1_finite_of_cover_charZero f)
    (schemeDivisorCrit1_finite_of_cover_charZero g)
    (schemeDivisorCrit1_finite_of_cover_charZero π) hcomm

/-- `lem:covers` for normal varieties in characteristic zero, expressed using
the actual divisor pushforwards and stalk ramification indices. -/
theorem scheme_pcf_of_ramified_cover_charZero
    {X Y : Scheme.{u}} (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsFinite π] [IsDominant π]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X] [NoetherianSpace X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormalScheme Y] [NoetherianSpace Y]
    [CharZero (X.presheaf.stalk (genericPoint X))]
    [CharZero (Y.presheaf.stalk (genericPoint Y))]
    (hcomm : g ≫ π = π ≫ f)
    (hpcf : (divDynOfFiniteDominantNormalCharZero g).IsPCF) :
    (divDynOfFiniteDominantNormalCharZero f).IsPCF :=
  (schemeRamifiedCoverCharZero f g π hcomm).pcf hpcf

#print axioms DivisorDynamics.pcSet_subset_ramifiedCoverBound
#print axioms DivisorDynamics.pcf_of_ramified_branch_union
#print axioms DivisorDynamics.RamifiedCover.finite_preimage
#print axioms DivisorDynamics.RamifiedCover.branch_union
#print axioms DivisorDynamics.RamifiedCover.pcSet_subset
#print axioms DivisorDynamics.RamifiedCover.pcf
#print axioms schemeRamifiedCover
#print axioms scheme_pcf_of_ramified_cover
#print axioms formallyEtale_stalkMap_genericPoint_of_cover_charZero
#print axioms schemeDivisorCrit1_finite_of_cover_charZero
#print axioms schemeRamifiedCoverCharZero
#print axioms scheme_pcf_of_ramified_cover_charZero

end Pcf
