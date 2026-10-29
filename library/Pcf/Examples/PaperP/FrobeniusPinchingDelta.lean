/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.FrobeniusPinchingGenerators
public import Pcf.Bounding.SchemeDeltaDynamics
public import Pcf.Bounding.AffineSchemeRamification
public import Pcf.Bounding.PointRamificationIdx
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.RingTheory.KrullDimension.PID

/-!
# The weighted local degree of the comparison in `ex:frobenius-pinching`

`paper-p.tex`, Example `ex:frobenius-pinching`, asserts that the comparison
`V(y) → B`, which in coordinates is `k[u]=k[x^p] ↪ k[x]`, has
`δ = p` at every closed point. Here `δ` is the manuscript's
`e·[κ(D):κ(fD)]_insep`, formalized as `Pcf.schemeDivisorDelta` of the actual
scheme morphism `Spec k[x] → Spec k[x^p]`.

The proof is valid over an arbitrary field `k` of characteristic `p`
(not only algebraically closed ones): `k[x]` is free of rank `p` over
`k[x^p]` with basis `1, x, …, x^(p-1)`, every `p`-th power of `k[x]` lies in
`k[x^p]`, so each prime has a unique prime above it and purely inseparable
residue extension, and Mathlib's `Σ e f = rank` gives `e·f = p`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.FrobeniusPinchingDelta

open Polynomial AlgebraicGeometry CategoryTheory IsLocalRing
open Pcf.Examples.PaperP.FrobeniusPinchingGenerators

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable (k : Type*) [Field k] (p : ℕ)

/-- Coefficients of `Σ_{j<p} x^j · g_j(x^p)`. -/
theorem coeff_sum_X_pow_mul_expand (hp : 0 < p) (g : Fin p → Polynomial k) (n : ℕ) :
    (∑ j : Fin p, (X : Polynomial k) ^ (j : ℕ) * expand k p (g j)).coeff n =
      (g ⟨n % p, Nat.mod_lt _ hp⟩).coeff (n / p) := by
  rw [finsetSum_coeff, Finset.sum_eq_single ⟨n % p, Nat.mod_lt _ hp⟩]
  · rw [coeff_X_pow_mul', ite_eq_left (Nat.mod_le n p), coeff_expand hp]
    have h := Nat.div_add_mod n p
    have hsub : n - n % p = p * (n / p) := by omega
    rw [hsub, ite_eq_left (dvd_mul_right p _), Nat.mul_div_cancel_left _ hp]
  · intro j _ hj
    rw [coeff_X_pow_mul']
    split_ifs with hjn
    · rw [coeff_expand hp]
      split_ifs with hdvd
      · exfalso
        obtain ⟨c, hc⟩ := hdvd
        have hn : n = j + p * c := by omega
        apply hj
        apply Fin.ext
        simp only [hn, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]
      · rfl
    · rfl
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem coeff_iterate_divX (f : Polynomial k) (i n : ℕ) :
    (divX^[i] f).coeff n = f.coeff (n + i) := by
  induction i generalizing n with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply', coeff_divX, ih]
      congr 1
      omega

/-- Every polynomial decomposes as `Σ_{j<p} x^j · g_j(x^p)`. -/
theorem eq_sum_X_pow_mul_expand (hp : 0 < p) (f : Polynomial k) :
    f = ∑ j : Fin p, (X : Polynomial k) ^ (j : ℕ) *
      expand k p (contract p (divX^[(j : ℕ)] f)) := by
  ext n
  rw [coeff_sum_X_pow_mul_expand k p hp, coeff_contract hp.ne', coeff_iterate_divX]
  congr 1
  have := Nat.div_add_mod n p
  simp only
  rw [mul_comm]
  omega

theorem axisPowers_smul_eq (a : axisPowers k p) (f : Polynomial k) :
    a • f = (a : Polynomial k) * f := rfl

/-- The basis `1, x, …, x^(p-1)` of `k[x]` over `k[x^p]`. -/
noncomputable def axisBasis (hp : 0 < p) : Module.Basis (Fin p) (axisPowers k p) (Polynomial k) :=
  Module.Basis.mk (v := fun j : Fin p => (X : Polynomial k) ^ (j : ℕ))
    (by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      choose h hh using fun j => axisPowerMap_surjective k p (g j)
      have hsum : (∑ j : Fin p, (X : Polynomial k) ^ (j : ℕ) * expand k p (h j)) = 0 := by
        rw [← hg]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [axisPowers_smul_eq, ← hh j, axisPowerMap_apply, mul_comm]
      have hi : h i = 0 := by
        ext m
        have := congrArg (fun q : Polynomial k => q.coeff (m * p + i)) hsum
        simp only [coeff_sum_X_pow_mul_expand k p hp, coeff_zero] at this
        have hmod : (m * p + (i : ℕ)) % p = i := by
          rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]
        have hdiv : (m * p + (i : ℕ)) / p = m := by
          rw [add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt i.isLt, zero_add]
        have hfin : (⟨(m * p + (i : ℕ)) % p, Nat.mod_lt _ hp⟩ : Fin p) = i := Fin.ext hmod
        rw [hfin, hdiv] at this
        simpa using this
      rw [← hh i, hi, map_zero])
    (by
      intro f _
      rw [eq_sum_X_pow_mul_expand k p hp f]
      refine Submodule.sum_mem _ fun j _ => ?_
      have : (X : Polynomial k) ^ (j : ℕ) * expand k p (contract p (divX^[(j : ℕ)] f)) =
          axisPowerMap k p (contract p (divX^[(j : ℕ)] f)) • (X : Polynomial k) ^ (j : ℕ) := by
        rw [axisPowers_smul_eq, axisPowerMap_apply, mul_comm]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

theorem axis_moduleFree (hp : 0 < p) : Module.Free (axisPowers k p) (Polynomial k) :=
  Module.Free.of_basis (axisBasis k p hp)

theorem axis_moduleFinite (hp : 0 < p) : Module.Finite (axisPowers k p) (Polynomial k) :=
  Module.Finite.of_basis (axisBasis k p hp)

/-- `k[x]` has rank `p` over `k[x^p]`. -/
theorem axis_finrank (hp : 0 < p) : Module.finrank (axisPowers k p) (Polynomial k) = p := by
  rw [Module.finrank_eq_card_basis (axisBasis k p hp), Fintype.card_fin]

variable [Fact p.Prime] [CharP k p]

/-- Every `p`-th power in `k[x]` lies in `k[x^p]`. -/
theorem exists_algebraMap_eq_pow (f : Polynomial k) :
    ∃ r : axisPowers k p, algebraMap (axisPowers k p) (Polynomial k) r = f ^ p := by
  refine ⟨axisPowerMap k p (map (frobenius k p) f), ?_⟩
  change (axisPowerMap k p (map (frobenius k p) f) : Polynomial k) = _
  rw [axisPowerMap_apply, ← map_expand, map_frobenius_expand]

/-- Primes of `k[x]` are determined by their contraction to `k[x^p]`. -/
theorem prime_eq_of_under_eq (q₁ q₂ : Ideal (Polynomial k)) [q₁.IsPrime] [q₂.IsPrime]
    (h : q₁.under (axisPowers k p) = q₂.under (axisPowers k p)) : q₁ = q₂ := by
  have key : ∀ (a b : Ideal (Polynomial k)) [a.IsPrime] [b.IsPrime],
      a.under (axisPowers k p) = b.under (axisPowers k p) → a ≤ b := by
    intro a b _ hb hab s hs
    obtain ⟨r, hr⟩ := exists_algebraMap_eq_pow k p s
    have hra : r ∈ a.under (axisPowers k p) := by
      rw [Ideal.under_def, Ideal.mem_comap, hr]
      exact Ideal.pow_mem_of_mem a hs p (Fact.out : p.Prime).pos
    rw [hab, Ideal.under_def, Ideal.mem_comap, hr] at hra
    exact hb.mem_of_pow_mem p hra
  exact le_antisymm (key q₁ q₂ h) (key q₂ q₁ h.symm)

/-- At every prime of `k[x]`, ramification index times inertia degree over
`k[x^p]` is `p`. -/
theorem ramificationIdx_mul_inertiaDeg (q : Ideal (Polynomial k)) [q.IsPrime] :
    q.ramificationIdx (axisPowers k p) * q.inertiaDeg (axisPowers k p) = p := by
  have hp := (Fact.out : p.Prime).pos
  haveI := axis_moduleFree k p hp
  haveI := axis_moduleFinite k p hp
  let P := q.under (axisPowers k p)
  haveI : Subsingleton (P.primesOver (Polynomial k)) := by
    constructor
    intro a b
    haveI := a.2.1
    haveI := b.2.1
    apply Subtype.ext
    apply prime_eq_of_under_eq k p
    rw [← a.2.2.over, ← b.2.2.over]
  let qo : P.primesOver (Polynomial k) := ⟨q, inferInstance, ⟨rfl⟩⟩
  haveI : Unique (P.primesOver (Polynomial k)) := uniqueOfSubsingleton qo
  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (Polynomial k)
  rw [Fintype.sum_unique, axis_finrank k p hp] at hsum
  have hdef : (default : P.primesOver (Polynomial k)) = qo := Subsingleton.elim _ _
  rw [hdef] at hsum
  exact hsum


section SpecMap

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The actual comparison morphism `Spec S → Spec R`. -/
noncomputable abbrev specAlgebraMap (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    Spec (.of S) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- The stalk ramification index of `Spec S → Spec R` is Mathlib's
`Ideal.ramificationIdx`, for a flat algebra. -/
theorem specAlgebraMap_ramificationIdx [Module.Flat R S]
    (d : Pcf.SchemeDivisorPoint (Spec (.of S))) :
    Pcf.schemeDivisorRamificationIdx (specAlgebraMap R S) d =
      (d.1 : PrimeSpectrum S).asIdeal.ramificationIdx R := by
  let f := algebraMap R S
  let q : PrimeSpectrum S := d.1
  let e := Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom f) q
  have hidx := Pcf.ramificationIdx_maximalIdeal_eq_of_ringEquiv
    ((specAlgebraMap R S).stalkMap q).hom
    (Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl)
    (Arrow.leftFunc.mapIso e).commRingCatIsoToRingEquiv
    (Arrow.rightFunc.mapIso e).commRingCatIsoToRingEquiv (by
      exact congrArg CommRingCat.Hom.hom e.hom.w)
  change Pcf.schemeDivisorRamificationIdx (specAlgebraMap R S) d = _ at hidx
  rw [hidx]
  let P : Ideal R := q.asIdeal.under R
  haveI : q.asIdeal.LiesOver P := ⟨rfl⟩
  letI : Algebra (Localization.AtPrime P) (Localization.AtPrime q.asIdeal) :=
    (Localization.localRingHom P q.asIdeal f rfl).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime P) (Localization.AtPrime q.asIdeal) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      exact (Localization.localRingHom_to_map P q.asIdeal f rfl a).symm)
  haveI : IsLocalHom (algebraMap (Localization.AtPrime P) (Localization.AtPrime q.asIdeal)) :=
    show IsLocalHom (Localization.localRingHom P q.asIdeal f rfl) from inferInstance
  exact Pcf.ramificationIdx_eq_of_localization_square P q.asIdeal

/-- The residue degree of `Spec S → Spec R`, computed on actual scheme
residue fields, is Mathlib's `Ideal.inertiaDeg`. -/
theorem specAlgebraMap_residue_finrank (q : PrimeSpectrum S) :
    letI := ((specAlgebraMap R S).residueFieldMap q).hom.toAlgebra
    Module.finrank ((Spec (.of R)).residueField ((specAlgebraMap R S) q))
      ((Spec (.of S)).residueField q) = q.asIdeal.inertiaDeg R := by
  let f := algebraMap R S
  let e := Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom f) q
  let e₁ : (Spec (.of R)).presheaf.stalk ((specAlgebraMap R S) q) ≃+*
      Localization.AtPrime (q.asIdeal.comap f) :=
    (Arrow.leftFunc.mapIso e).commRingCatIsoToRingEquiv
  let e₂ : (Spec (.of S)).presheaf.stalk q ≃+* Localization.AtPrime q.asIdeal :=
    (Arrow.rightFunc.mapIso e).commRingCatIsoToRingEquiv
  let ψ := Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl
  have hcomm : ψ.comp e₁.toRingHom = e₂.toRingHom.comp ((specAlgebraMap R S).stalkMap q).hom :=
    congrArg CommRingCat.Hom.hom e.hom.w
  let P : Ideal R := q.asIdeal.under R
  haveI : q.asIdeal.LiesOver P := ⟨rfl⟩
  letI : Algebra (Localization.AtPrime P) (Localization.AtPrime q.asIdeal) :=
    (Localization.localRingHom P q.asIdeal f rfl).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime P) (Localization.AtPrime q.asIdeal) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      exact (Localization.localRingHom_to_map P q.asIdeal f rfl a).symm)
  haveI : IsLocalHom (algebraMap (Localization.AtPrime P) (Localization.AtPrime q.asIdeal)) :=
    show IsLocalHom (Localization.localRingHom P q.asIdeal f rfl) from inferInstance
  rw [Ideal.inertiaDeg_def]
  letI := ((specAlgebraMap R S).residueFieldMap q).hom.toAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv (ResidueField.mapEquiv e₁)
    (ResidueField.mapEquiv e₂) ?_
  apply Ideal.Quotient.ringHom_ext
  ext x
  change ResidueField.map ψ (ResidueField.map (e₁ : _ →+* _) (residue _ x)) =
    ResidueField.map (e₂ : _ →+* _)
      (ResidueField.map ((specAlgebraMap R S).stalkMap q).hom (residue _ x))
  simp only [ResidueField.map_residue]
  exact congrArg (residue _) (congrArg (fun g => g x) hcomm)

/-- Frobenius-in-image on rings implies it on the actual stalk maps. -/
theorem specAlgebraMap_stalk_frobenius (n : ℕ)
    (hfrob : ∀ s : S, ∃ r : R, algebraMap R S r = s ^ n) (q : PrimeSpectrum S) :
    ∀ s : (Spec (.of S)).presheaf.stalk q,
      ∃ r, ((specAlgebraMap R S).stalkMap q).hom r = s ^ n := by
  let f := algebraMap R S
  let e := Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom f) q
  let e₁ : (Spec (.of R)).presheaf.stalk ((specAlgebraMap R S) q) ≃+*
      Localization.AtPrime (q.asIdeal.comap f) :=
    (Arrow.leftFunc.mapIso e).commRingCatIsoToRingEquiv
  let e₂ : (Spec (.of S)).presheaf.stalk q ≃+* Localization.AtPrime q.asIdeal :=
    (Arrow.rightFunc.mapIso e).commRingCatIsoToRingEquiv
  let ψ := Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl
  have hcomm : ψ.comp e₁.toRingHom = e₂.toRingHom.comp ((specAlgebraMap R S).stalkMap q).hom :=
    congrArg CommRingCat.Hom.hom e.hom.w
  have hloc : ∀ t : Localization.AtPrime q.asIdeal, ∃ r, ψ r = t ^ n := by
    intro t
    obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl t
    obtain ⟨ra, hra⟩ := hfrob a
    obtain ⟨rb, hrb⟩ := hfrob (b : S)
    have hrb' : rb ∈ (q.asIdeal.comap f).primeCompl := by
      intro hmem
      apply b.2
      change f rb ∈ q.asIdeal at hmem
      rw [show f rb = (b : S) ^ n from hrb] at hmem
      exact q.2.mem_of_pow_mem n hmem
    refine ⟨IsLocalization.mk' _ ra ⟨rb, hrb'⟩, ?_⟩
    rw [Localization.localRingHom_mk', ← IsLocalization.mk'_pow]
    congr 1
    exact Subtype.ext hrb
  intro s
  obtain ⟨r, hr⟩ := hloc (e₂ s)
  refine ⟨e₁.symm r, e₂.injective ?_⟩
  have := congrArg (fun g => g (e₁.symm r)) hcomm
  refine Eq.trans this.symm ?_
  change ψ (e₁ (e₁.symm r)) = _
  rw [RingEquiv.apply_symm_apply, hr, map_pow]

end SpecMap

section Comparison

universe u

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The manuscript's comparison `V(y) → B`, in the coordinates `V(y)=Spec k[x]` and
`B=Spec k[x^p]` (`FrobeniusPinchingGenerators.axisRestriction_eq_zero_iff` identifies
`k[x^p]` with the coordinate ring of `B ⊂ Spec R`). -/
noncomputable abbrev comparisonSchemeMap :
    Spec (.of (Polynomial k)) ⟶ Spec (.of (axisPowers k p)) :=
  specAlgebraMap (axisPowers k p) (Polynomial k)

omit [CharP k p] in
/-- The comparison is finite. -/
theorem comparisonSchemeMap_finite : IsFinite (comparisonSchemeMap k p) := by
  haveI := axis_moduleFinite k p (Fact.out : p.Prime).pos
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- The residue extensions of the comparison are purely inseparable. -/
theorem comparison_residue_isPurelyInseparable (q : PrimeSpectrum (Polynomial k)) :
    letI := ((comparisonSchemeMap k p).residueFieldMap q).hom.toAlgebra
    IsPurelyInseparable ((Spec (.of (axisPowers k p))).residueField ((comparisonSchemeMap k p) q))
      ((Spec (.of (Polynomial k))).residueField q) := by
  letI := ((comparisonSchemeMap k p).residueFieldMap q).hom.toAlgebra
  let K := (Spec (.of (axisPowers k p))).residueField ((comparisonSchemeMap k p) q)
  let L := (Spec (.of (Polynomial k))).residueField q
  have hpK : ((p : ℕ) : K) = 0 := by
    let φ : axisPowers k p →+* K := ((Scheme.ΓSpecIso (.of (axisPowers k p))).inv ≫
      (Spec (.of (axisPowers k p))).presheaf.germ ⊤ _ trivial ≫
      (Spec (.of (axisPowers k p))).residue _).hom
    have h1 : ((p : ℕ) : axisPowers k p) = 0 := by
      apply Subtype.ext
      simp
    rw [← map_natCast φ p, h1, map_zero]
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpK
  haveI : ExpChar K p := ExpChar.prime (Fact.out : p.Prime)
  rw [isPurelyInseparable_iff_pow_mem K p]
  intro x
  obtain ⟨s, rfl⟩ := (Spec (.of (Polynomial k))).residue_surjective q x
  obtain ⟨r, hr⟩ := specAlgebraMap_stalk_frobenius p (exists_algebraMap_eq_pow k p) q s
  refine ⟨1, (Spec (.of (axisPowers k p))).residue _ r, ?_⟩
  rw [pow_one, ← map_pow, ← hr]
  exact congrArg (fun g => g.hom r)
    (Scheme.residue_residueFieldMap (comparisonSchemeMap k p) q)

/-- **`ex:frobenius-pinching`, `δ = p`.** The manuscript's weighted local degree
`δ = e·[κ(D):κ(fD)]_insep`, computed from the actual stalk and residue-field maps of the
comparison `Spec k[x] → Spec k[x^p]`, equals `p` at every integral effective divisor
(over any field `k` of characteristic `p`).

`paper-p.tex` correspondence: Example 4.5 (`ex:frobenius-pinching`). -/
theorem comparison_schemeDivisorDelta (d : Pcf.SchemeDivisorPoint (Spec (.of (Polynomial k)))) :
    Pcf.schemeDivisorDelta (comparisonSchemeMap k p) d = p := by
  haveI := axis_moduleFree k p (Fact.out : p.Prime).pos
  let q : PrimeSpectrum (Polynomial k) := d.1
  unfold Pcf.schemeDivisorDelta
  rw [specAlgebraMap_ramificationIdx d]
  letI := ((comparisonSchemeMap k p).residueFieldMap q).hom.toAlgebra
  haveI := comparison_residue_isPurelyInseparable k p q
  rw [IsPurelyInseparable.finInsepDegree_eq]
  have hres := specAlgebraMap_residue_finrank (R := axisPowers k p) (S := Polynomial k) q
  change _ * Module.finrank _ _ = p
  rw [hres]
  exact ramificationIdx_mul_inertiaDeg k p q.asIdeal

/-- Every closed point of `V(y)=Spec k[x]` is an integral effective divisor. -/
theorem closedPoint_coheight (x : Spec (.of (Polynomial k))) (hx : IsClosed ({x} : Set _)) :
    Order.coheight x = 1 := by
  rw [← AlgebraicGeometry.idealHeight_eq_coheight]
  haveI : (x : PrimeSpectrum (Polynomial k)).asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hx
  exact IsPrincipalIdealRing.height_eq_one_of_isMaximal _ (Polynomial.not_isField k)

/-- **`ex:frobenius-pinching`, closed-point form.** At every closed point of
`V(y)`, the comparison's `δ` equals `p`. -/
theorem comparison_delta_at_closedPoint (x : Spec (.of (Polynomial k)))
    (hx : IsClosed ({x} : Set _)) :
    Pcf.schemeDivisorDelta (comparisonSchemeMap k p) ⟨x, closedPoint_coheight k x hx⟩ = p :=
  comparison_schemeDivisorDelta k p _

end Comparison

/-- The commutative square of coordinate rings `R → k[x,y]`, `R → k[x^p]`,
`k[x,y] → k[x]`, `k[x^p] ↪ k[x]`: the comparison is the restriction of the
normalization to `V(y) → B`. -/
theorem axis_square_commutes (k : Type*) [Field k] (p : ℕ) (a : ring k p) :
    ((axisRestriction k p a : axisPowers k p) : Polynomial k) = axis k (a : Plane k) := rfl

#print axioms coeff_sum_X_pow_mul_expand
#print axioms axisBasis
#print axioms axis_finrank
#print axioms exists_algebraMap_eq_pow
#print axioms prime_eq_of_under_eq
#print axioms ramificationIdx_mul_inertiaDeg
#print axioms specAlgebraMap_ramificationIdx
#print axioms specAlgebraMap_residue_finrank
#print axioms specAlgebraMap_stalk_frobenius
#print axioms comparisonSchemeMap_finite
#print axioms comparison_residue_isPurelyInseparable
#print axioms comparison_schemeDivisorDelta
#print axioms comparison_delta_at_closedPoint
#print axioms axis_square_commutes

end Pcf.Examples.PaperP.FrobeniusPinchingDelta
