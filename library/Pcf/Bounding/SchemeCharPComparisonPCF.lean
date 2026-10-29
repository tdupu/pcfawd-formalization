/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeGenericSeparabilityMap

/-!
# Weighted PCF descent through finite scheme comparisons

This formalizes the divisor dynamics in `paper-p.tex`, Lemma
`lem:pcf-transfer-charp`. The separable comparison case follows from
the actual scheme square. A second result handles the purely
inseparable factor once its constant local degree has been established.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

set_option linter.style.haveILetI false

/-- The separable comparison case of `paper-p.tex`, Lemma
`lem:pcf-transfer-charp`, for actual finite dominant normal scheme
morphisms. Generic separability of the lower map follows from the
commuting square, so it is not an input. -/
theorem schemePCF_descent_of_separableComparison
    {X Y : Scheme.{u}} (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsFinite π] [IsDominant π]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [NoetherianSpace X] [NoetherianSpace Y]
    (hcomm : g ≫ π = π ≫ f)
    (hsep_g : IsGenericallySeparableSchemeMap g)
    (hsep_π : IsGenericallySeparableSchemeMap π)
    (hPCF_g : (schemeDeltaDynamicsOfFiniteDominantNormal g).IsPCF) :
    IsGenericallySeparableSchemeMap f ∧
      (schemeDeltaDynamicsOfFiniteDominantNormal f).IsPCF := by
  have hsep_f := isGenericallySeparable_of_finite_commuting_square
    f g π hcomm hsep_g
  exact ⟨hsep_f, schemeDeltaDynamics_isPCF_of_genericallySeparable_square
    f g π hcomm hsep_f hsep_π hPCF_g⟩

/-- The purely inseparable comparison part of the paper's proof at
the level of actual normal scheme divisors. The displayed hypothesis
is the geometric identity `δ_ρ(D)=q`, where `q` is the degree of the
purely inseparable function-field extension. -/
theorem schemePCF_descent_of_constantComparison
    {M Y : Scheme.{u}} (hM : M ⟶ M) (h : Y ⟶ Y) (ρ : Y ⟶ M)
    [IsFinite hM] [IsDominant hM] [IsFinite h] [IsDominant h]
    [IsFinite ρ] [IsDominant ρ]
    [IsIntegral M] [IsIntegral Y]
    [IsLocallyNoetherian M] [IsLocallyNoetherian Y]
    [IsNormalScheme M] [IsNormalScheme Y]
    (hcomm : h ≫ ρ = ρ ≫ hM)
    (q : ℕ) (hq : 0 < q)
    (hδρ : ∀ d : SchemeDivisorPoint Y, schemeDivisorDelta ρ d = q)
    (hPCF_h : (schemeDeltaDynamicsOfFiniteDominantNormal h).IsPCF) :
    (schemeDeltaDynamicsOfFiniteDominantNormal hM).IsPCF := by
  let D := schemeDeltaDynamicsOfFiniteDominantNormal hM
  let E := schemeDeltaDynamicsOfFiniteDominantNormal h
  let ρDiv : SchemeDivisorPoint Y → SchemeDivisorPoint M :=
    fun d => d.mapFiniteDominantNormal ρ
  apply D.isPCF_of_constant_comparison E ρDiv
    (SchemeDivisorPoint.mapFiniteDominantNormal_surjective ρ)
    (fun d => schemeDeltaDynamics_comparison_comm hM h ρ hcomm d)
    q hq
  · intro d
    have htower := schemeDeltaDynamics_comparison_tower_of_isFinite
      hM h ρ hcomm d
    change D.delta (ρDiv d) * schemeDivisorDelta ρ d =
      schemeDivisorDelta ρ (E.step d) * E.delta d at htower
    rw [hδρ d, hδρ (E.step d)] at htower
    simpa only [mul_comm] using htower
  · exact hPCF_h

/-- The complete divisor-dynamical descent once the comparison has
been factored through a separable map `σ` and a constant-weight
purely inseparable map `ρ`. The finite normalization factorization
and `δ_ρ=q` are the remaining geometric constructions. -/
theorem schemePCF_descent_of_factorizedComparison
    {X M Y : Scheme.{u}}
    (f : X ⟶ X) (hM : M ⟶ M) (h : Y ⟶ Y)
    (σ : M ⟶ X) (ρ : Y ⟶ M)
    [IsFinite f] [IsDominant f]
    [IsFinite hM] [IsDominant hM]
    [IsFinite h] [IsDominant h]
    [IsFinite σ] [IsDominant σ]
    [IsFinite ρ] [IsDominant ρ]
    [IsIntegral X] [IsIntegral M] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian M]
    [IsLocallyNoetherian Y]
    [IsNormalScheme X] [IsNormalScheme M] [IsNormalScheme Y]
    [NoetherianSpace X] [NoetherianSpace M]
    (hcommρ : h ≫ ρ = ρ ≫ hM)
    (hcommσ : hM ≫ σ = σ ≫ f)
    (hsep_h : IsGenericallySeparableSchemeMap h)
    (hsep_σ : IsGenericallySeparableSchemeMap σ)
    (q : ℕ) (hq : 0 < q)
    (hδρ : ∀ d : SchemeDivisorPoint Y, schemeDivisorDelta ρ d = q)
    (hPCF_h : (schemeDeltaDynamicsOfFiniteDominantNormal h).IsPCF) :
    IsGenericallySeparableSchemeMap f ∧
      (schemeDeltaDynamicsOfFiniteDominantNormal f).IsPCF := by
  have hsep_hM := isGenericallySeparable_of_finite_commuting_square
    hM h ρ hcommρ hsep_h
  have hPCF_hM := schemePCF_descent_of_constantComparison
    hM h ρ hcommρ q hq hδρ hPCF_h
  exact schemePCF_descent_of_separableComparison
    f hM σ hcommσ hsep_hM hsep_σ hPCF_hM

#print axioms schemePCF_descent_of_separableComparison
#print axioms schemePCF_descent_of_constantComparison
#print axioms schemePCF_descent_of_factorizedComparison

end Pcf
