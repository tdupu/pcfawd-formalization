/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeWiring
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Ambient divisor dynamics of an actual scheme endomorphism

The ramification index below is Mathlib's local length invariant applied to the
actual stalk map. Positivity uses quasi-finiteness, not a finiteness assumption
on the stalk algebra (which need not be a finite module).

Finite dominance over a normal locally Noetherian integral target proves
surjectivity and finiteness of the divisor-map fibers. For self-maps,
`divisorDynamicsOfFiniteDominantNormal` uses finiteness of the actual critical divisor
locus. The characteristic-zero constructor derives that finiteness from the
finite dominant geometry and Noetherianity: the generic stalk extension is
finite and separable, hence formally étale. None of these inputs asserts PCF
or a bounding conclusion.

Ramification indices multiply under composition because the intermediate
codimension-one stalk is a DVR and the upper stalk extension is torsion free.
Consequently `DivisorDynamics.iterateRamificationIdx` agrees with the ramification index of the
actual scheme iterate. The comparison with affine-coordinate `heightOneRamificationIdx` remains
separate.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

set_option linter.style.haveILetI false

/-- Quasi-finiteness suffices for positivity of the local length ramification
index: the local fiber ring is Artinian and nonzero. -/
theorem ramificationIdx_pos_of_quasiFinite
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.QuasiFinite R S] (q : Ideal S) [q.IsPrime] :
    0 < q.ramificationIdx R := by
  let p := q.under R
  let Sq := Localization.AtPrime q
  rw [Ideal.ramificationIdx_def]
  apply ENat.toNat_pos
  · rw [← pos_iff_ne_zero, Module.length_pos_iff, Submodule.Quotient.nontrivial_iff,
      IsScalarTower.algebraMap_eq R S, ← Ideal.map_map, ← lt_top_iff_ne_top]
    grw [Ideal.map_mono Ideal.map_comap_le, Localization.AtPrime.map_eq_maximalIdeal]
    exact (IsLocalRing.maximalIdeal.isMaximal _).lt_top
  · rw [Module.length_eq_of_surjective (R := Sq ⧸ p.map (algebraMap R Sq))
        Ideal.Quotient.mk_surjective,
      Module.length_ne_top_iff, ← isArtinianRing_iff_isFiniteLength]
    infer_instance

/-- The codimension-one ramification index of the actual stalk homomorphism.
Both the base stalk and its action on the source stalk are determined by `f`. -/
noncomputable def schemeDivisorRamificationIdx {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : SchemeDivisorPoint X) : ℕ :=
  letI := (f.stalkMap x.1).hom.toAlgebra
  (IsLocalRing.maximalIdeal (X.presheaf.stalk x.1)).ramificationIdx
    (Y.presheaf.stalk (f x.1))

/-- A codimension-one stalk of a normal locally Noetherian integral scheme is
a DVR. Thus the stalk length invariant is taken on precisely the local rings
used for divisorial ramification. -/
theorem SchemeDivisorPoint.stalk_isDiscreteValuationRing
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    (x : SchemeDivisorPoint X) : IsDiscreteValuationRing (X.presheaf.stalk x.1) := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x.1) isOpen_univ
  let U : X.affineOpens := ⟨W, hW⟩
  let y : (U : X.Opens) := ⟨x.1, hxW⟩
  letI : Nonempty (U : X.Opens) := ⟨y⟩
  letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  letI : IsIntegrallyClosed Γ(X, U) := IsNormalScheme.component_integrallyClosed U
  letI : Algebra Γ(X, U) (X.presheaf.stalk x.1) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf y
  let p := (U.2.primeIdealOf y).asIdeal
  have hp : p.height = 1 := by
    dsimp only [p, y]
    rw [← pointClosureIdealSheaf_ideal x.1 U hxW]
    exact pointClosureIdealSheaf_ideal_height x U hxW
  letI : IsLocalization.AtPrime (X.presheaf.stalk x.1) p :=
    U.2.isLocalization_stalk y
  letI : IsDiscreteValuationRing (Localization.AtPrime p) :=
    isDiscreteValuationRing_localizationAtPrime_of_heightOne p hp
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime p) (X.presheaf.stalk x.1)).toRingEquiv

/-- Quasi-compact dominance between integral schemes makes every stalk
homomorphism injective. -/
theorem stalkMap_injective_of_dominant_integral
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsDominant f] [QuasiCompact f]
    [IsIntegral X] [IsIntegral Y] (x : X) :
    Function.Injective (f.stalkMap x).hom := by
  letI : IsSchemeTheoreticallyDominant f :=
    IsSchemeTheoreticallyDominant.of_isDominant f
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f x)) isOpen_univ
  apply hU.stalkMap_injective f x hxU
  intro a ha
  rw [f.germ_stalkMap_apply] at ha
  have ha' : f.app U a = 0 :=
    (germ_injective_of_isIntegral X x hxU) (ha.trans (map_zero _).symm)
  have ha'' : a = 0 := (f.app_injective U) (ha'.trans (map_zero _).symm)
  simp [ha'']

set_option backward.isDefEq.respectTransparency false in
/-- Ramification indices of actual stalk maps multiply under composition.
The upper stalk extension is torsion free over the intermediate DVR and hence flat. -/
theorem schemeDivisorRamificationIdx_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormalScheme Y]
    (x : SchemeDivisorPoint X) :
    schemeDivisorRamificationIdx (f ≫ g) x =
      schemeDivisorRamificationIdx g (x.mapFiniteDominantNormal f) * schemeDivisorRamificationIdx f
          x := by
  let R := Z.presheaf.stalk (g (f x.1))
  let S := Y.presheaf.stalk (f x.1)
  let T := X.presheaf.stalk x.1
  letI : Algebra R S := (g.stalkMap (f x.1)).hom.toAlgebra
  letI : Algebra S T := (f.stalkMap x.1).hom.toAlgebra
  letI : Algebra R T := ((f ≫ g).stalkMap x.1).hom.toAlgebra
  letI : IsLocalHom (algebraMap S T) :=
    show IsLocalHom (f.stalkMap x.1).hom from inferInstance
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' (by
    change ((f ≫ g).stalkMap x.1).hom =
      (f.stalkMap x.1).hom.comp (g.stalkMap (f x.1)).hom
    rw [Scheme.Hom.stalkMap_comp]
    rfl)
  letI : IsDiscreteValuationRing S :=
    (x.mapFiniteDominantNormal f).stalk_isDiscreteValuationRing
  letI : FaithfulSMul S T := (faithfulSMul_iff_algebraMap_injective S T).mpr
    (stalkMap_injective_of_dominant_integral f x.1)
  letI : Module.Flat S T := inferInstance
  exact Ideal.ramificationIdx_tower (R := R) (IsLocalRing.maximalIdeal S)
    (IsLocalRing.maximalIdeal T)

/-- The actual stalk ramification index is positive for a quasi-finite morphism. -/
theorem schemeDivisorRamificationIdx_pos {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] (x : SchemeDivisorPoint X) :
    0 < schemeDivisorRamificationIdx f x := by
  letI := (f.stalkMap x.1).hom.toAlgebra
  letI : Algebra.QuasiFinite (Y.presheaf.stalk (f x.1)) (X.presheaf.stalk x.1) :=
    f.quasiFiniteAt x.1
  exact ramificationIdx_pos_of_quasiFinite _

/-- Formal étaleness of the actual stalk implies ramification index one. -/
theorem schemeDivisorRamificationIdx_eq_one_of_formallyEtale
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : SchemeDivisorPoint X) (hx : (f.stalkMap x.1).hom.FormallyEtale) :
    schemeDivisorRamificationIdx f x = 1 := by
  letI := (f.stalkMap x.1).hom.toAlgebra
  letI : Algebra.EssFiniteType (Y.presheaf.stalk (f x.1)) (X.presheaf.stalk x.1) :=
    LocallyOfFiniteType.stalkMap f x.1
  letI : Algebra.FormallyEtale (Y.presheaf.stalk (f x.1)) (X.presheaf.stalk x.1) := hx
  exact Ideal.ramificationIdx_eq_one _ _

/-- A ramified divisor belongs to the actual non-formally-étale stalk locus. -/
theorem mem_schemeDivisorNonEtaleLocus_of_one_lt_ramificationIdx
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : SchemeDivisorPoint X) (hx : 1 < schemeDivisorRamificationIdx f x) :
    x ∈ schemeDivisorNonEtaleLocus f := by
  intro hetale
  have h := schemeDivisorRamificationIdx_eq_one_of_formallyEtale f x hetale
  omega

/-- Finite dominant morphisms to normal locally Noetherian integral schemes
preserve the codimension of every point, not only divisor points. -/
theorem coheight_apply_eq_of_finite_dominant_normal
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormalScheme Y]
    (x : X) : Order.coheight (f x) = Order.coheight x := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f x)) isOpen_univ
  let U : Y.affineOpens := ⟨W, hW⟩
  let V := finitePreimageAffine f U
  have hxV : x ∈ (V : X.Opens) := hxW
  letI : Nonempty (U : Y.Opens) := ⟨⟨f x, hxW⟩⟩
  letI : Nonempty (V : X.Opens) := ⟨⟨x, hxV⟩⟩
  letI : Algebra Γ(Y, U) Γ(X, V) := (f.app U).hom.toAlgebra
  letI : Module.Finite Γ(Y, U) Γ(X, V) := moduleFinite_finitePreimageAffine f U
  letI : FaithfulSMul Γ(Y, U) Γ(X, V) := faithfulSMul_finitePreimageAffine f U
  letI : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian U
  letI : IsNoetherianRing Γ(X, V) := IsNoetherianRing.of_finite Γ(Y, U) _
  letI : IsIntegrallyClosed Γ(Y, U) := IsNormalScheme.component_integrallyClosed U
  let hU : IsAffineOpen (U : Y.Opens) := U.2
  let hV : IsAffineOpen (V : X.Opens) := V.2
  let Q : AlgebraicGeometry.Spec Γ(X, V) := V.2.primeIdealOf ⟨x, hxV⟩
  let q : AlgebraicGeometry.Spec Γ(Y, U) := U.2.primeIdealOf ⟨f x, hxW⟩
  have hAlg : algebraMap Γ(Y, U) Γ(X, V) = (f.appLE U V le_rfl).hom := by
    change (f.app U).hom = (f.appLE U V le_rfl).hom
    exact congr_arg CommRingCat.Hom.hom f.appLE_eq_app.symm
  have hcontract : Q.asIdeal.under Γ(Y, U) = q.asIdeal := by
    change Q.asIdeal.comap (algebraMap Γ(Y, U) Γ(X, V)) = q.asIdeal
    rw [hAlg]
    exact congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE (U : Y.Opens) U.2
        (V : X.Opens) V.2 le_rfl hxV)
  have htarget := AlgebraicGeometry.coheight_eq_of_isOpenImmersion
    (x := q) hU.fromSpec
  have hsource := AlgebraicGeometry.coheight_eq_of_isOpenImmersion
    (x := Q) hV.fromSpec
  rw [hU.fromSpec_primeIdealOf] at htarget
  rw [hV.fromSpec_primeIdealOf] at hsource
  rw [htarget, hsource, ← AlgebraicGeometry.idealHeight_eq_coheight,
    ← AlgebraicGeometry.idealHeight_eq_coheight, ← hcontract]
  exact height_under_eq_of_finite_of_normal Q.asIdeal

/-- Lying over for the actual divisor map of a finite dominant morphism. -/
theorem SchemeDivisorPoint.mapFiniteDominantNormal_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormalScheme Y] :
    Function.Surjective (fun x : SchemeDivisorPoint X ↦
      x.mapFiniteDominantNormal f) := by
  intro y
  obtain ⟨x, hx⟩ := f.surjective y.1
  have hcodim : Order.coheight x = 1 := by
    rw [← coheight_apply_eq_of_finite_dominant_normal f x, hx]
    exact y.2
  exact ⟨⟨x, hcodim⟩, Subtype.ext hx⟩

/-- The canonical divisor pushforward has finite fibers. -/
theorem SchemeDivisorPoint.mapFiniteDominantNormal_finite_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormalScheme Y]
    (y : SchemeDivisorPoint Y) :
    ((fun x : SchemeDivisorPoint X ↦ x.mapFiniteDominantNormal f) ⁻¹' {y}).Finite :=
  schemeDivisorMap_finite_fiber f (coheight_apply_eq_one f) y

/-- The actual ambient dynamics, assuming only finiteness of the actual
codimension-one non-étale locus in addition to the finite normal geometry.
This assumption concerns a single morphism and contains no orbit condition. -/
noncomputable def divisorDynamicsOfFiniteDominantNormal
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    (hcrit : (schemeDivisorNonEtaleLocus f).Finite) : DivisorDynamics (SchemeDivisorPoint X) where
  step x := x.mapFiniteDominantNormal f
  ramificationIdx := schemeDivisorRamificationIdx f
  ramificationIdx_pos := schemeDivisorRamificationIdx_pos f
  step_surjective := SchemeDivisorPoint.mapFiniteDominantNormal_surjective f
  step_image_ramified_finite := by
    refine (hcrit.image (fun x ↦ x.mapFiniteDominantNormal f)).subset ?_
    rintro y ⟨x, hxy, hx⟩
    exact ⟨x, mem_schemeDivisorNonEtaleLocus_of_one_lt_ramificationIdx f x hx, hxy⟩

/-- Under a proper Noetherian critical locus, its finitely many divisorial
components give the branch-finiteness input automatically. An étale stalk
witnesses properness since the source is irreducible. -/
noncomputable def divisorDynamicsOfFiniteDominantNormalOfExistsFormallyEtale
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    [NoetherianSpace (schemeNonEtaleLocus f)]
    (hetale : ∃ x : X, (f.stalkMap x).hom.FormallyEtale) :
    DivisorDynamics (SchemeDivisorPoint X) :=
  divisorDynamicsOfFiniteDominantNormal f
    (schemeDivisorNonEtaleLocus_finite_of_isClosed_of_exists_formallyEtale f
      (isClosed_schemeNonEtaleLocus f) hetale)

/-- For a globally Noetherian scheme, the critical locus is automatically
Noetherian; generic étaleness is the only extra input to the constructor. -/
noncomputable def divisorDynamicsOfFiniteDominantNormalNoetherian
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X] [NoetherianSpace X]
    (hetale : ∃ x : X, (f.stalkMap x).hom.FormallyEtale) :
    DivisorDynamics (SchemeDivisorPoint X) :=
  divisorDynamicsOfFiniteDominantNormalOfExistsFormallyEtale f hetale

/-- In characteristic zero, a finite dominant endomorphism of a Noetherian
normal integral scheme supplies its actual divisor dynamics with no separate
generic-étaleness or branch-finiteness hypothesis. -/
noncomputable def divisorDynamicsOfFiniteDominantNormalCharZero
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X] [NoetherianSpace X]
    [CharZero (X.presheaf.stalk (genericPoint X))] :
    DivisorDynamics (SchemeDivisorPoint X) :=
  divisorDynamicsOfFiniteDominantNormalNoetherian f
    ⟨genericPoint X,
      formallyEtale_stalkMap_genericPoint_of_finite_dominant_charZero f⟩

/-- In any characteristic, separability of the function-field extension
supplies the actual divisor dynamics of a finite dominant normal self-map.
The branch finiteness is proved from generic étaleness and Noetherianity;
no PCF or orbit condition is part of this constructor. Its `branch` records
only indices greater than one. In positive characteristic, identifying it
with the manuscript's branch set additionally requires separability of every
residue extension at a divisor, to be obtained from prime-to-`p` monodromy. -/
noncomputable def divisorDynamicsOfFiniteDominantNormalSeparable
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X] [NoetherianSpace X]
    (hsep : IsGenericallySeparable f) :
    DivisorDynamics (SchemeDivisorPoint X) :=
  divisorDynamicsOfFiniteDominantNormalNoetherian f
    ⟨genericPoint X,
      formallyEtale_stalkMap_genericPoint_of_finite_dominant_separable f hsep⟩

@[simp]
theorem divisorDynamicsOfFiniteDominantNormal_step_val
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    (hcrit : (schemeDivisorNonEtaleLocus f).Finite) (x : SchemeDivisorPoint X) :
    ((divisorDynamicsOfFiniteDominantNormal f hcrit).step x).1 = f x.1 := rfl

@[simp]
theorem divisorDynamicsOfFiniteDominantNormal_ramificationIdx
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    (hcrit : (schemeDivisorNonEtaleLocus f).Finite) (x : SchemeDivisorPoint X) :
    (divisorDynamicsOfFiniteDominantNormal f hcrit).ramificationIdx x = schemeDivisorRamificationIdx
        f x := rfl

/-- The abstract iterated step agrees with the actual scheme iterate on points. -/
theorem divisorDynamicsOfFiniteDominantNormal_iterate_step_val
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    (hcrit : (schemeDivisorNonEtaleLocus f).Finite) (m : ℕ) (x : SchemeDivisorPoint X) :
    (((divisorDynamicsOfFiniteDominantNormal f hcrit).step)^[m] x).1 =
      (CategoryTheory.End.of f ^ m).asHom.base x.1 :=
  schemeDivisorMap_iterate_val f (coheight_apply_eq_one f) m x

/-- The stalk ramification index of the identity is one. -/
@[simp] theorem schemeDivisorRamificationIdx_id {X : Scheme.{u}} (x : SchemeDivisorPoint X) :
    schemeDivisorRamificationIdx (𝟙 X) x = 1 := by
  apply schemeDivisorRamificationIdx_eq_one_of_formallyEtale
  rw [Scheme.Hom.stalkMap_id]
  change (RingHom.id _).FormallyEtale
  rw [RingHom.FormallyEtale]
  infer_instance

/-- The product of the one-step ramification indices is the ramification
index of the actual scheme iterate. -/
theorem divisorDynamicsOfFiniteDominantNormal_iterateRamificationIdx
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    (hcrit : (schemeDivisorNonEtaleLocus f).Finite) (m : ℕ) (x : SchemeDivisorPoint X) :
    (divisorDynamicsOfFiniteDominantNormal f hcrit).iterateRamificationIdx m x =
      schemeDivisorRamificationIdx (CategoryTheory.End.of f ^ m).asHom x := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
      rw [show m + 1 = 1 + m by omega, DivisorDynamics.iterateRamificationIdx_add,
        DivisorDynamics.iterateRamificationIdx_one, Function.iterate_one, ih, add_comm, pow_succ]
      exact (Nat.mul_comm _ _).trans
        (schemeDivisorRamificationIdx_comp f (CategoryTheory.End.of f ^ m).asHom x).symm

/-- A finite dominant map from an integral normal scheme to a Noetherian
characteristic-zero integral scheme transfers the Noetherian and
characteristic-zero hypotheses needed to construct the source's divisor
dynamics.  This is the situation of a finite normalization morphism. -/
noncomputable def divisorDynamicsOfFiniteNormalization
    {A N : Scheme.{u}} (gN : N ⟶ N) (nu : N ⟶ A)
    [IsFinite gN] [IsDominant gN]
    [IsFinite nu] [IsDominant nu]
    [IsIntegral A] [IsIntegral N] [IsLocallyNoetherian N] [IsNormalScheme N]
    [NoetherianSpace A]
    [CharZero (A.presheaf.stalk (genericPoint A))] :
    DivisorDynamics (SchemeDivisorPoint N) := by
  letI : CompactSpace N := QuasiCompact.compactSpace_of_compactSpace nu
  letI : IsNoetherian N := {}
  have hnu : nu (genericPoint N) = genericPoint A :=
    map_genericPoint_eq_of_isDominant nu
  let e :=
    (A.presheaf.stalkCongr (Inseparable.of_eq hnu)).commRingCatIsoToRingEquiv
  have hfield : IsField (A.presheaf.stalk (nu (genericPoint N))) :=
    e.toMulEquiv.isField (Field.toIsField _)
  letI : Field (A.presheaf.stalk (nu (genericPoint N))) := hfield.toField
  letI : CharZero (A.presheaf.stalk (nu (genericPoint N))) :=
    charZero_of_injective_ringHom e.symm.injective
  letI : CharZero (N.presheaf.stalk (genericPoint N)) :=
    charZero_of_injective_ringHom (nu.stalkMap (genericPoint N)).hom.injective
  exact divisorDynamicsOfFiniteDominantNormalCharZero gN

/-- The normalization constructor retains the actual ramification indices of
all scheme iterates. -/
theorem divisorDynamicsOfFiniteNormalization_iterateRamificationIdx
    {A N : Scheme.{u}} (gN : N ⟶ N) (nu : N ⟶ A)
    [IsFinite gN] [IsDominant gN]
    [IsFinite nu] [IsDominant nu]
    [IsIntegral A] [IsIntegral N] [IsLocallyNoetherian N] [IsNormalScheme N]
    [NoetherianSpace A]
    [CharZero (A.presheaf.stalk (genericPoint A))]
    (m : ℕ) (Q : SchemeDivisorPoint N) :
    (divisorDynamicsOfFiniteNormalization gN nu).iterateRamificationIdx m Q =
      schemeDivisorRamificationIdx (CategoryTheory.End.of gN ^ m).asHom Q := by
  unfold divisorDynamicsOfFiniteNormalization divisorDynamicsOfFiniteDominantNormalCharZero
    divisorDynamicsOfFiniteDominantNormalNoetherian
    divisorDynamicsOfFiniteDominantNormalOfExistsFormallyEtale
  exact divisorDynamicsOfFiniteDominantNormal_iterateRamificationIdx gN _ m Q

/-- Construct the two-carrier normalization package from actual scheme morphisms.

The target divisor map and the normalization divisor map are obtained from the
finite-type codimension theorem, the normalized dynamics is the actual stalk
ramification dynamics of `gN`, and the commuting and finite-fiber properties of
normalization are proved from the commuting square and finiteness of `nu`.

The remaining `hU1` argument is exactly the comparison between ramification of
the normalized iterate and formal unramifiedness of the unnormalized iterate.
It is kept visible because neither a divisor-set map nor a commuting square
identifies the relevant local rings or ramification indices. -/
noncomputable def schemeNormalizationUnnormalizedDynamicsOfFiniteType
    (k : Type*) [Field k]
    {A N : Scheme.{u}} (g : A ⟶ A) (gN : N ⟶ N) (nu : N ⟶ A)
    [IsFinite g] [IsDominant g] [LocallyOfFinitePresentation g]
    [IsFinite gN] [IsDominant gN]
    [IsFinite nu] [IsDominant nu]
    [IsIntegral A] [IsIntegral N] [IsLocallyNoetherian N] [IsNormalScheme N]
    [NoetherianSpace A]
    [CharZero (A.presheaf.stalk (genericPoint A))]
    [∀ U : A.affineOpens, Algebra k Γ(A, U)]
    [∀ U : A.affineOpens, Algebra.FiniteType k Γ(A, U)]
    (hsquare : gN ≫ nu = nu ≫ g)
    (hU1 : ∀ m Q,
      1 < (divisorDynamicsOfFiniteNormalization gN nu).iterateRamificationIdx m Q →
        schemeDivisorMap nu (coheight_apply_eq_one_of_finiteType nu k) Q ∈
          schemeDivisorNonUnramifiedLocus (CategoryTheory.End.of g ^ m).asHom) :
    SchemeNormalizationUnnormalizedDynamics A (SchemeDivisorPoint N) := {
    selfMap := g
    finite := inferInstance
    dominant := inferInstance
    finitePresentation := inferInstance
    selfMap_preserves_divisors := coheight_apply_eq_one_of_finiteType g k
    normalized := divisorDynamicsOfFiniteNormalization gN nu
    normalization := schemeDivisorMap nu (coheight_apply_eq_one_of_finiteType nu k)
    normalization_step := fun Q ↦ by
      exact schemeDivisorMap_comm_of_comm gN g nu
        (coheight_apply_eq_one gN)
        (coheight_apply_eq_one_of_finiteType g k)
        (coheight_apply_eq_one_of_finiteType nu k) hsquare Q
    normalization_finite_fiber := fun Q ↦
      schemeDivisorMap_finite_fiber nu
        (coheight_apply_eq_one_of_finiteType nu k) Q
    mem_nonUnramifiedLocus_of_one_lt_ramificationIdx := hU1
    integral := inferInstance
    noetherian := inferInstance
    charZero := inferInstance }

/-- Build the invariant-divisor PCF setup with the ambient dynamics forced to be
the divisor dynamics of the given endomorphism.  In particular, the distinguished
prime is the actual invariant divisor `A`, and its invariance is proved from `hA`.

This removes the possibility of pairing the geometric Step-0 data for `f` with an
unrelated abstract ambient `DivisorDynamics`.  The remaining inputs are the normalized
restriction package, the finite exceptional sets, and the literal Step-0 data. -/
noncomputable def InvariantDivisorSchemeNormalizationPCFSetup.ofActualAmbient
    {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormalScheme X] [NoetherianSpace X]
    [CharZero (X.presheaf.stalk (genericPoint X))]
    (A : SchemeDivisorPoint X) (hA : f A.1 = A.1)
    {PN : Type*}
    (restriction : SchemeNormalizationUnnormalizedDynamics
      (pointClosureIdealSheaf A.1).subscheme PN)
    (restriction_selfMap : restriction.selfMap = A.invariantClosureMap f hA)
    (singularPrimes : Set (SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme))
    (singularPrimes_finite : singularPrimes.Finite)
    (meets : SchemeDivisorPoint X →
      Set (SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme))
    (meets_finite : ∀ E, E ≠ A → (meets E).Finite)
    (localData : ∀ (m : ℕ), 1 ≤ m →
      ∀ (Q : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme), Q ∉ singularPrimes →
      (∀ E ∈ (divisorDynamicsOfFiniteDominantNormalCharZero f).iterate m |>.branch,
        E ≠ A → Q ∉ meets E) →
      ∀ (Q' : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme),
        restriction.toNormalizationUnnormalizedDynamics.step^[m] Q' = Q →
        InvariantDivisorCorrectionLocalData X f A m Q Q') :
    InvariantDivisorSchemeNormalizationPCFSetup X f A hA
      (SchemeDivisorPoint X) PN where
  ambient := divisorDynamicsOfFiniteDominantNormalCharZero f
  fixedPrime := A
  fixed := Subtype.ext hA
  restriction := restriction
  restriction_selfMap := restriction_selfMap
  singularPrimes := singularPrimes
  singularPrimes_finite := singularPrimes_finite
  meets := meets
  meets_finite := meets_finite
  localData := localData

#print axioms SchemeDivisorPoint.stalk_isDiscreteValuationRing
#print axioms stalkMap_injective_of_dominant_integral
#print axioms schemeDivisorRamificationIdx_comp
#print axioms schemeDivisorRamificationIdx_id
#print axioms divisorDynamicsOfFiniteDominantNormal_iterateRamificationIdx
#print axioms divisorDynamicsOfFiniteNormalization_iterateRamificationIdx
#print axioms coheight_apply_eq_of_finite_dominant_normal
#print axioms SchemeDivisorPoint.mapFiniteDominantNormal_finite_fiber
#print axioms divisorDynamicsOfFiniteDominantNormalNoetherian
#print axioms divisorDynamicsOfFiniteDominantNormalCharZero
#print axioms divisorDynamicsOfFiniteDominantNormal_iterate_step_val
#print axioms divisorDynamicsOfFiniteNormalization
#print axioms schemeNormalizationUnnormalizedDynamicsOfFiniteType
#print axioms InvariantDivisorSchemeNormalizationPCFSetup.ofActualAmbient

end Pcf
