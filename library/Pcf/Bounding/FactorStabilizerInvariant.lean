/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.ReducedFibreFactors
public import Mathlib.GroupTheory.Coset.Card

/-!
# Fixed fields of factor stabilizers

For a finite reduced fibre, the primitive idempotent selecting a field
factor can be used to turn a stabilizer-fixed element of that factor
into a globally fixed element. This is the last invariant-theoretic
step in `latex/paper-p.tex`, Lemma `lem:allcodim-monodromy`.
-/

@[expose] public section

namespace Pcf

universe u v w x y

open scoped Pointwise
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {F : Type u} {A : Type v} {L : Type w}
  {G : Type x} {ι : Type y}
  [Field F] [CommRing A] [Field L]
  [Algebra F A] [Algebra F L]
  [Group G] [MulSemiringAction G A]
  [SMulCommClass G F A] [Algebra.IsInvariant F A G]
  [MulAction G ι] [DecidableEq ι]

section ActualReducedFibre


variable [FiniteDimensional F A] [IsReduced A]

/-- The primitive idempotent of a component in the actual finite
reduced fibre. -/
noncomputable def reducedFactorSelector (m : MaximalSpectrum A) : A :=
  by
    classical
    exact (reducedFiniteAlgebraEquivPi (F := F) (A := A)).symm (Pi.single m 1)

@[simp] theorem reducedFactorSelector_projection_self
    (m : MaximalSpectrum A) :
    Ideal.Quotient.mk m.asIdeal (reducedFactorSelector (F := F) m) = 1 := by
  classical
  change (reducedFiniteAlgebraEquivPi (F := F) (A := A)
    (reducedFactorSelector (F := F) m)) m = _
  simp [reducedFactorSelector]

@[simp] theorem reducedFactorSelector_projection_other
    (m n : MaximalSpectrum A) (hne : n ≠ m) :
    Ideal.Quotient.mk n.asIdeal (reducedFactorSelector (F := F) m) = 0 := by
  classical
  change (reducedFiniteAlgebraEquivPi (F := F) (A := A)
    (reducedFactorSelector (F := F) m)) n = _
  simp [reducedFactorSelector, hne]

/-- Under the group action, the selected factor moves with its
maximal ideal. This formulation uses the inverse image ideal so it
does not require a separately chosen action on maximal spectra. -/
theorem reducedFactorSelector_action_projection_other
    (m n n' : MaximalSpectrum A) (g : G)
    (hn' : n'.asIdeal = g⁻¹ • n.asIdeal) (hne : n' ≠ m) :
    Ideal.Quotient.mk n.asIdeal (g • reducedFactorSelector (F := F) m) = 0 := by
  have hmem : reducedFactorSelector (F := F) m ∈ n'.asIdeal := by
    exact (Ideal.Quotient.eq_zero_iff_mem).mp
      (reducedFactorSelector_projection_other (F := F) m n' hne)
  have hmem' : g • reducedFactorSelector (F := F) m ∈ n.asIdeal := by
    rw [hn', Ideal.mem_inv_pointwise_smul_iff] at hmem
    exact hmem
  exact (Ideal.Quotient.eq_zero_iff_mem).mpr hmem'

theorem reducedFactorSelector_action_projection_self
    (m n : MaximalSpectrum A) (g : G)
    (hn : m.asIdeal = g⁻¹ • n.asIdeal) :
    Ideal.Quotient.mk n.asIdeal (g • reducedFactorSelector (F := F) m) = 1 := by
  have hmem : 1 - reducedFactorSelector (F := F) m ∈ m.asIdeal := by
    have h := reducedFactorSelector_projection_self (F := F) m
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    simp [h]
  have hmem' : g • (1 - reducedFactorSelector (F := F) m) ∈ n.asIdeal := by
    rw [hn, Ideal.mem_inv_pointwise_smul_iff] at hmem
    exact hmem
  apply Eq.symm
  apply sub_eq_zero.mp
  apply (Ideal.Quotient.eq_zero_iff_mem).mpr
  simpa [smul_sub, smul_one] using hmem'

/-- The inverse image of a maximal component under an automorphism
is another maximal component. -/
noncomputable def actedMaximalFactor (g : G) (n : MaximalSpectrum A) :
    MaximalSpectrum A :=
  ⟨g⁻¹ • n.asIdeal, by
    rw [Ideal.pointwise_smul_eq_comap]
    exact Ideal.IsMaximal.comap_bijective
      (MulSemiringAction.toRingAut G A g⁻¹).symm
      (MulSemiringAction.toRingAut G A g⁻¹).symm.bijective n.isMaximal⟩

/-- The primitive selector evaluates to one precisely on its moved
factor, and to zero on every other factor. -/
theorem reducedFactorSelector_action_projection
    [DecidableEq (MaximalSpectrum A)]
    (m n : MaximalSpectrum A) (g : G) :
    Ideal.Quotient.mk n.asIdeal (g • reducedFactorSelector (F := F) m) =
      if (actedMaximalFactor (A := A) g n) = m then 1 else 0 := by
  classical
  split_ifs with h
  · exact reducedFactorSelector_action_projection_self
      (F := F) m n g (by
        have hh := congrArg MaximalSpectrum.asIdeal h
        exact hh.symm)
  · exact reducedFactorSelector_action_projection_other
      (F := F) m n (actedMaximalFactor (A := A) g n) g
        (show (actedMaximalFactor (A := A) g n).asIdeal = g⁻¹ • n.asIdeal from rfl) h

/-- Fixing a component is equivalent to fixing its maximal ideal. -/
theorem actedMaximalFactor_eq_iff_stabilizer
    (m : MaximalSpectrum A) (g : G) :
    actedMaximalFactor (A := A) g m = m ↔ g • m.asIdeal = m.asIdeal := by
  constructor
  · intro h
    have hh : g⁻¹ • m.asIdeal = m.asIdeal :=
      congrArg MaximalSpectrum.asIdeal h
    calc
      g • m.asIdeal = g • (g⁻¹ • m.asIdeal) := congrArg (g • ·) hh.symm
      _ = m.asIdeal := smul_inv_smul g _
  · intro h
    apply MaximalSpectrum.ext
    change g⁻¹ • m.asIdeal = m.asIdeal
    calc
      g⁻¹ • m.asIdeal = g⁻¹ • (g • m.asIdeal) := congrArg (g⁻¹ • ·) h.symm
      _ = m.asIdeal := inv_smul_smul g _

end ActualReducedFibre

section FiniteGroup

variable [Fintype G]

/-- The orbit sum of any element is fixed by the whole finite group. -/
theorem orbit_sum_invariant (a : A) :
    ∀ h : G, h • (∑ g : G, g • a) = ∑ g : G, g • a := by
  intro h
  rw [Finset.smul_sum]
  simpa only [mul_smul] using
    (Function.Bijective.sum_comp (Group.mulLeft_bijective h) (fun g : G => g • a))

/-- An idempotent selecting one factor makes every element fixed by
that factor's stabilizer a scalar. The selector property follows from
the product-of-fields decomposition; the nonzero stabilizer order is
the prime-to-`p` input. -/
theorem factor_fixed_of_orbit_selector
    (i : ι) (π : A →ₐ[F] L) (e : A)
    (hselector : ∀ g : G,
      π (g • e) = if g • i = i then 1 else 0)
    (horder : ((Fintype.card (MulAction.stabilizer G i) : ℕ) : F) ≠ 0)
    (a : A)
    (hfixed : ∀ g : G, g • i = i → π (g • a) = π a) :
    ∃ c : F, algebraMap F L c = π a := by
  let z : A := ∑ g : G, g • (e * a)
  obtain ⟨c, hc⟩ :=
    Algebra.IsInvariant.isInvariant (A := F) (B := A) (G := G) z
      (orbit_sum_invariant (G := G) (e * a))
  let H := MulAction.stabilizer G i
  have hz : π z = (Fintype.card H : F) • π a := by
    change π (∑ g : G, g • (e * a)) = _
    rw [map_sum]
    simp_rw [smul_mul', map_mul, hselector]
    simp only [ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter]
    calc
      ∑ g ∈ Finset.univ.filter (fun g : G => g • i = i), π (g • a) =
          ∑ g ∈ Finset.univ.filter (fun g : G => g • i = i), π a := by
            apply Finset.sum_congr rfl
            intro g hg
            exact hfixed g (Finset.mem_filter.mp hg).2
      _ = (Fintype.card H : F) • π a := by
        simp [H, Fintype.card_subtype, Algebra.smul_def]
  have hza : π z = algebraMap F L c := by
    rw [← hc]
    exact π.commutes c
  have ha : π a = (Fintype.card H : F)⁻¹ • π z := by
    rw [hz, smul_smul, inv_mul_cancel₀ horder, one_smul]
  refine ⟨(Fintype.card H : F)⁻¹ * c, ?_⟩
  rw [map_mul, ← hza]
  simpa only [Algebra.smul_def] using ha.symm

section ActualFactorFixedField

variable [FiniteDimensional F A] [IsReduced A]

/-- For the actual residue-field factor of a finite reduced fibre,
every element fixed by its ideal stabilizer lies in the base field.
The group order assumption is exactly the prime-to-characteristic
hypothesis of `lem:allcodim-monodromy`. -/
theorem reducedFactor_stabilizer_fixed_is_scalar
    (p : ℕ) (hp : p.Prime) [CharP F p]
    (horder : (Fintype.card G).Coprime p)
    (m : MaximalSpectrum A) (a : A)
    (hfixed : ∀ g : G, g • m.asIdeal = m.asIdeal →
      Ideal.Quotient.mk m.asIdeal (g • a) = Ideal.Quotient.mk m.asIdeal a) :
    ∃ c : F, algebraMap F (A ⧸ m.asIdeal) c =
      Ideal.Quotient.mk m.asIdeal a := by
  classical
  letI : Field (A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  let H := MulAction.stabilizer G m.asIdeal
  have hcop : (Fintype.card H).Coprime p :=
    Nat.Coprime.of_dvd_left
      (by simpa only [Nat.card_eq_fintype_card] using H.card_subgroup_dvd_card)
      horder
  have hunit : IsUnit ((Fintype.card H : ℕ) : F) :=
    (CharP.isUnit_natCast_iff hp).mpr
      (hp.coprime_iff_not_dvd.mp hcop.symm)
  have hnz : ((Fintype.card H : ℕ) : F) ≠ 0 := hunit.ne_zero
  apply factor_fixed_of_orbit_selector
    (F := F) (G := G) (ι := Ideal A)
    m.asIdeal (Ideal.Quotient.mkₐ F m.asIdeal)
    (reducedFactorSelector (F := F) m)
  · intro g
    change Ideal.Quotient.mk m.asIdeal
      (g • reducedFactorSelector (F := F) m) = _
    rw [reducedFactorSelector_action_projection (F := F) m m g]
    simp only [actedMaximalFactor_eq_iff_stabilizer]
  · exact hnz
  · exact hfixed

/-- The previous result for a residue-field element, without a
chosen representative. -/
theorem reducedFactor_stabilizer_fixed_field_eq_base
    (p : ℕ) (hp : p.Prime) [CharP F p]
    (horder : (Fintype.card G).Coprime p)
    (m : MaximalSpectrum A) (x : A ⧸ m.asIdeal)
    (hfixed : ∀ g : G, g • m.asIdeal = m.asIdeal →
      ∀ a : A, Ideal.Quotient.mk m.asIdeal a = x →
        Ideal.Quotient.mk m.asIdeal (g • a) = x) :
    ∃ c : F, algebraMap F (A ⧸ m.asIdeal) c = x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact reducedFactor_stabilizer_fixed_is_scalar (F := F) p hp horder m a
    (fun g hg => hfixed g hg a rfl)

/-- The same fixed-field equality using mathlib's actual stabilizer
homomorphism on the residue field. -/
theorem reducedFactor_stabilizerHom_fixed_field_eq_base
    (p : ℕ) (hp : p.Prime) [CharP F p]
    (horder : (Fintype.card G).Coprime p)
    (m : MaximalSpectrum A) (x : A ⧸ m.asIdeal)
    (hx : ∀ g : MulAction.stabilizer G m.asIdeal,
      Ideal.Quotient.stabilizerHom m.asIdeal (⊥ : Ideal F) G g x = x) :
    ∃ c : F, algebraMap F (A ⧸ m.asIdeal) c = x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply reducedFactor_stabilizer_fixed_is_scalar (F := F) p hp horder m a
  intro g hg
  simpa only [Ideal.Quotient.stabilizerHom_apply,
    MulAction.subgroup_smul_def] using
    hx ⟨g, hg⟩

/-- The fixed set of the actual stabilizer action on a residue-field
factor is exactly the scalar copy of the base field. -/
theorem reducedFactor_stabilizerHom_fixed_set_eq_range
    (p : ℕ) (hp : p.Prime) [CharP F p]
    (horder : (Fintype.card G).Coprime p)
    (m : MaximalSpectrum A) :
    {x : A ⧸ m.asIdeal | ∀ g : MulAction.stabilizer G m.asIdeal,
      Ideal.Quotient.stabilizerHom m.asIdeal (⊥ : Ideal F) G g x = x} =
      Set.range (algebraMap F (A ⧸ m.asIdeal)) := by
  ext x
  constructor
  · intro hx
    exact reducedFactor_stabilizerHom_fixed_field_eq_base
      (F := F) p hp horder m x hx
  · rintro ⟨c, rfl⟩ g
    have h := (Ideal.Quotient.stabilizerHom m.asIdeal
      (⊥ : Ideal F) G g).commutes (Ideal.Quotient.mk (⊥ : Ideal F) c)
    simpa only [Ideal.Quotient.algebraMap_mk_of_liesOver,
      Ideal.Quotient.mk_algebraMap] using h

end ActualFactorFixedField

end FiniteGroup

#print axioms orbit_sum_invariant
#print axioms factor_fixed_of_orbit_selector
#print axioms reducedFactor_stabilizer_fixed_is_scalar
#print axioms reducedFactor_stabilizer_fixed_field_eq_base
#print axioms reducedFactor_stabilizerHom_fixed_field_eq_base
#print axioms reducedFactor_stabilizerHom_fixed_set_eq_range

end Pcf
