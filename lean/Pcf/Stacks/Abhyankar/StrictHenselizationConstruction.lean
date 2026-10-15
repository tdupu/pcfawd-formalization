/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.Under.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# A small category of pointed etale neighbourhoods

This file begins the construction of a strict henselization as a filtered colimit of pointed
etale neighbourhoods.  To avoid a universe-sized category of all algebras, an object is encoded
by an explicit finite polynomial presentation.  Its underlying algebra is the corresponding
quotient, together with an etaleness witness and a point in a fixed geometric residue field.

Tensor products give a common refinement of any two objects.  Two parallel pointed maps are
equalized by the etale localization selected by the idempotent diagonal ideal of their source.
This proves that the presentation-coded category is filtered.
-/

@[expose] public section

open CategoryTheory Limits
open scoped TensorProduct

universe u

namespace Pcf.Stacks

/-- The algebra represented by a finite list of polynomial relations. -/
abbrev PresentedEtaleAlgebra (R : Type u) [CommRing R] (n m : ℕ)
    (relation : Fin m → MvPolynomial (Fin n) R) : Type u :=
  MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range relation)

/-- A small, presentation-coded pointed etale neighbourhood of `R` at an `R`-algebra `Ω`.

The intended application takes `R` local and `Ω` to be a separable closure of its residue field.
The small presentation code is essential: storing an arbitrary carrier `Type u` would make the
index category live in `Type (u + 1)`, too large for the same-universe ring colimit. -/
structure PointedEtaleNeighborhood (R Ω : Type u) [CommRing R] [CommRing Ω] [Algebra R Ω] where
  /-- Number of polynomial generators. -/
  vars : ℕ
  /-- Number of polynomial relations. -/
  rels : ℕ
  /-- The chosen finite relation family. -/
  relation : Fin rels → MvPolynomial (Fin vars) R
  /-- The presented algebra is etale over the base. -/
  etale : Algebra.Etale R (PresentedEtaleAlgebra R vars rels relation)
  /-- The chosen geometric point. -/
  point : PresentedEtaleAlgebra R vars rels relation →ₐ[R] Ω

namespace PointedEtaleNeighborhood

variable (R Ω : Type u) [CommRing R] [CommRing Ω] [Algebra R Ω]

instance : CoeSort (PointedEtaleNeighborhood R Ω) (Type u) where
  coe X := PresentedEtaleAlgebra R X.vars X.rels X.relation

instance (X : PointedEtaleNeighborhood R Ω) : Algebra.Etale R X := X.etale

/-- A morphism of pointed etale neighbourhoods is an algebra map commuting with the points. -/
@[ext]
structure Hom (X Y : PointedEtaleNeighborhood R Ω) where
  /-- The underlying algebra map. -/
  hom : X →ₐ[R] Y
  /-- Compatibility with the chosen geometric points. -/
  point_comp : Y.point.comp hom = X.point

noncomputable instance : Category (PointedEtaleNeighborhood R Ω) where
  Hom := Hom R Ω
  id X := ⟨AlgHom.id R X, by simp⟩
  comp f g := ⟨g.hom.comp f.hom, by rw [← AlgHom.comp_assoc, g.point_comp, f.point_comp]⟩
  id_comp _ := by ext; rfl
  comp_id _ := by ext; rfl
  assoc _ _ _ := by ext; rfl

@[simp]
theorem id_hom (X : PointedEtaleNeighborhood R Ω) : Hom.hom (𝟙 X) = AlgHom.id R X := rfl

@[simp]
theorem comp_hom {X Y Z : PointedEtaleNeighborhood R Ω} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Hom.hom (f ≫ g) = g.hom.comp f.hom := rfl

variable {R Ω}

/-- The presented quotient associated to a finite presentation is isomorphic to the algebra it
presents. -/
noncomputable def presentationModelEquiv {S : Type u} [CommRing S] [Algebra R S]
    {n m : ℕ} (P : Algebra.Presentation R S (Fin n) (Fin m)) :
    PresentedEtaleAlgebra R n m P.relation ≃ₐ[R] S :=
  (Ideal.quotientEquivAlgOfEq R P.span_range_relation_eq_ker).trans
    (P.quotientEquiv.restrictScalars R)

/-- Encode any etale algebra with a chosen point by Mathlib's chosen finite presentation. -/
noncomputable def ofEtaleAlgebra (S : Type u) [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (point : S →ₐ[R] Ω) : PointedEtaleNeighborhood R Ω := by
  let P := Algebra.Presentation.ofFinitePresentation R S
  exact
    { vars := Algebra.Presentation.ofFinitePresentationVars R S
      rels := Algebra.Presentation.ofFinitePresentationRels R S
      relation := P.relation
      etale := Algebra.Etale.of_equiv (presentationModelEquiv P).symm
      point := point.comp (presentationModelEquiv P).toAlgHom }

/-- The comparison from the presentation-coded model back to the original etale algebra. -/
noncomputable def ofEtaleAlgebraEquiv (S : Type u) [CommRing S] [Algebra R S]
    [Algebra.Etale R S] (point : S →ₐ[R] Ω) :
    ofEtaleAlgebra S point ≃ₐ[R] S :=
  presentationModelEquiv (Algebra.Presentation.ofFinitePresentation R S)

@[simp]
theorem ofEtaleAlgebra_point_comp_equiv (S : Type u) [CommRing S] [Algebra R S]
    [Algebra.Etale R S] (point : S →ₐ[R] Ω) :
    (ofEtaleAlgebra S point).point.comp (ofEtaleAlgebraEquiv S point).symm.toAlgHom = point := by
  ext x
  change point ((presentationModelEquiv (Algebra.Presentation.ofFinitePresentation R S))
    ((presentationModelEquiv (Algebra.Presentation.ofFinitePresentation R S)).symm x)) = point x
  rw [AlgEquiv.apply_symm_apply]

/-- Lift a pointed algebra map into the chosen presentation-coded model of its codomain. -/
noncomputable def homToOfEtaleAlgebra {X : PointedEtaleNeighborhood R Ω}
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (point : S →ₐ[R] Ω) (f : X →ₐ[R] S) (hf : point.comp f = X.point) :
    X ⟶ ofEtaleAlgebra S point where
  hom := (ofEtaleAlgebraEquiv S point).symm.toAlgHom.comp f
  point_comp := by
    ext x
    change point ((ofEtaleAlgebraEquiv S point)
      ((ofEtaleAlgebraEquiv S point).symm (f x))) = X.point x
    rw [AlgEquiv.apply_symm_apply]
    exact DFunLike.congr_fun hf x

/-- The point on the tensor product of two pointed neighbourhoods. -/
noncomputable def tensorPoint (X Y : PointedEtaleNeighborhood R Ω) :
    TensorProduct R X Y →ₐ[R] Ω :=
  Algebra.TensorProduct.lift X.point Y.point (fun _ _ ↦ Commute.all _ _)

noncomputable instance (X Y : PointedEtaleNeighborhood R Ω) :
    Algebra.Etale R (TensorProduct R X Y) := by
  let _ : Algebra.Etale X (TensorProduct R X Y) := Algebra.Etale.baseChange R Y X
  exact Algebra.Etale.comp R X (TensorProduct R X Y)

/-- The tensor-product common refinement, encoded again by a finite presentation. -/
noncomputable def tensor (X Y : PointedEtaleNeighborhood R Ω) :
    PointedEtaleNeighborhood R Ω :=
  ofEtaleAlgebra (TensorProduct R X Y) (tensorPoint (R := R) (Ω := Ω) X Y)

/-- The first canonical map into the tensor-product common refinement. -/
noncomputable def toTensorLeft (X Y : PointedEtaleNeighborhood R Ω) : X ⟶ tensor X Y :=
  by
    change X ⟶ ofEtaleAlgebra (TensorProduct R X Y)
      (tensorPoint (R := R) (Ω := Ω) X Y)
    exact homToOfEtaleAlgebra (TensorProduct R X Y)
      (tensorPoint (R := R) (Ω := Ω) X Y) Algebra.TensorProduct.includeLeft <| by
      ext x
      simp [tensorPoint]

/-- The second canonical map into the tensor-product common refinement. -/
noncomputable def toTensorRight (X Y : PointedEtaleNeighborhood R Ω) : Y ⟶ tensor X Y :=
  by
    change Y ⟶ ofEtaleAlgebra (TensorProduct R X Y)
      (tensorPoint (R := R) (Ω := Ω) X Y)
    exact homToOfEtaleAlgebra (TensorProduct R X Y)
      (tensorPoint (R := R) (Ω := Ω) X Y) Algebra.TensorProduct.includeRight <| by
      ext y
      simp [tensorPoint]

/-- The category of pointed etale neighbourhoods is nonempty. -/
noncomputable instance : Nonempty (PointedEtaleNeighborhood R Ω) :=
  ⟨ofEtaleAlgebra R (Algebra.ofId R Ω)⟩

/-- Any two pointed etale neighbourhoods have a common refinement.  This is the object half of
filteredness; the parallel-map equalization half requires localization at the pointed etale
equalizer locus. -/
theorem exists_common_refinement (X Y : PointedEtaleNeighborhood R Ω) :
    ∃ Z : PointedEtaleNeighborhood R Ω, Nonempty (X ⟶ Z) ∧ Nonempty (Y ⟶ Z) :=
  ⟨tensor X Y, ⟨toTensorLeft X Y⟩, ⟨toTensorRight X Y⟩⟩

/-- Two parallel pointed etale maps become equal after an etale localization of their target.

The diagonal ideal of the source is generated by an idempotent because the source is formally
unramified and essentially of finite type over `R`.  Its image `d` in the target vanishes at the
chosen point.  Localizing away from `1 - d` therefore retains the point and kills `d`, hence kills
every basic difference `1 ⊗ x - x ⊗ 1` and equalizes the two maps. -/
theorem exists_equalizing_refinement {X Y : PointedEtaleNeighborhood R Ω} (f g : X ⟶ Y) :
    ∃ Z : PointedEtaleNeighborhood R Ω, ∃ h : Y ⟶ Z, f ≫ h = g ≫ h := by
  let I := KaehlerDifferential.ideal R X
  have hI : IsIdempotentElem I :=
    (Ideal.cotangent_subsingleton_iff I).mp (by
      change Subsingleton Ω[X⁄R]
      infer_instance)
  obtain ⟨e, he, hspan⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg I (KaehlerDifferential.ideal_fg R X)).mp hI
  let p : X ⊗[R] X →ₐ[R] Y := Algebra.TensorProduct.productMap f.hom g.hom
  let d : Y := p e
  have hd : IsIdempotentElem d := by
    change d * d = d
    simp only [d, ← map_mul, he.eq]
  have hpcomp : Y.point.comp p = X.point.comp (Algebra.TensorProduct.lmul' R) := by
    ext x
    · simpa [p] using DFunLike.congr_fun f.point_comp x
    · simpa [p] using DFunLike.congr_fun g.point_comp x
  have heI : e ∈ I := by
    rw [hspan]
    exact Ideal.mem_span_singleton_self e
  have hlmule : Algebra.TensorProduct.lmul' R e = 0 := by
    rw [RingHom.mem_ker] at heI
    exact heI
  have hpointd : Y.point d = 0 := by
    change (Y.point.comp p) e = 0
    rw [hpcomp]
    simp [hlmule]
  let L := Localization.Away (1 - d)
  let pointL : L →ₐ[R] Ω := IsLocalization.Away.liftAlgHom (1 - d) (f := Y.point) (by
    rw [map_sub, map_one, hpointd, sub_zero]
    exact isUnit_one)
  let q : Y →ₐ[R] L := IsScalarTower.toAlgHom R Y L
  have hpointLq : pointL.comp q = Y.point := by
    ext y
    simp [pointL, q]
  have hdzero : q d = 0 := by
    apply (IsLocalization.Away.algebraMap_isUnit (1 - d) (S := L)).mul_left_cancel
    change q (1 - d) * q d = q (1 - d) * 0
    rw [← map_mul]
    simp [hd.one_sub_mul_self]
  have hqfg : q.comp f.hom = q.comp g.hom := by
    ext x
    have hxI : (1 : X) ⊗ₜ[R] x - x ⊗ₜ[R] (1 : X) ∈ I :=
      KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R x
    rw [hspan, Ideal.mem_span_singleton'] at hxI
    obtain ⟨a, ha⟩ := hxI
    have h := congrArg q (congrArg p ha)
    simp only [map_sub, p, Algebra.TensorProduct.productMap_apply_tmul] at h
    rw [map_mul, show p e = d by rfl, map_mul, hdzero, mul_zero] at h
    have h' : 0 = q (g.hom x) - q (f.hom x) := by
      simpa only [map_mul, map_one, one_mul, mul_one] using h
    exact (sub_eq_zero.mp h'.symm).symm
  let Z := ofEtaleAlgebra L pointL
  let h : Y ⟶ Z := homToOfEtaleAlgebra L pointL q hpointLq
  refine ⟨Z, h, ?_⟩
  apply Hom.ext
  ext x
  change (ofEtaleAlgebraEquiv L pointL).symm (q (f.hom x)) =
    (ofEtaleAlgebraEquiv L pointL).symm (q (g.hom x))
  rw [show q (f.hom x) = q (g.hom x) from DFunLike.congr_fun hqfg x]

/-- The small category of presentation-coded pointed etale neighbourhoods is filtered. -/
instance : IsFiltered (PointedEtaleNeighborhood R Ω) where
  cocone_objs X Y := ⟨tensor X Y, toTensorLeft X Y, toTensorRight X Y, trivial⟩
  cocone_maps := fun _ _ f g ↦ exists_equalizing_refinement f g

/-- The diagram of presentation-coded pointed etale neighbourhoods as `R`-algebras. -/
noncomputable def functor :
    PointedEtaleNeighborhood R Ω ⥤ Under (CommRingCat.of R) where
  obj X := CommRingCat.mkUnder (CommRingCat.of R) X
  map f := AlgHom.toUnder f.hom
  map_id X := by ext x; rfl
  map_comp f g := by ext x; rfl

/-- The chosen points form a cocone in the category of `R`-algebras. -/
noncomputable def pointCocone : Cocone (functor (R := R) (Ω := Ω)) where
  pt := CommRingCat.mkUnder (CommRingCat.of R) Ω
  ι :=
    { app := fun X ↦ X.point.toUnder
      naturality := fun X Y f ↦ by
        ext x
        exact DFunLike.congr_fun f.point_comp x }

/-- The colimit object in the undercategory of `R`. -/
noncomputable def colimitObj : Under (CommRingCat.of R) :=
  colimit (functor (R := R) (Ω := Ω))

/-- The filtered colimit `R`-algebra of the small category of pointed etale neighbourhoods. -/
abbrev Colimit (R₁ Ω₁ : Type u) [CommRing R₁] [CommRing Ω₁] [Algebra R₁ Ω₁] : Type u :=
  (colimitObj (R := R₁) (Ω := Ω₁)).right

noncomputable instance : Algebra R (Colimit R Ω) :=
  (colimitObj (R := R) (Ω := Ω)).hom.hom.toAlgebra

/-- The canonical `R`-algebra map from a neighbourhood into the filtered colimit. -/
noncomputable def toColimit (X : PointedEtaleNeighborhood R Ω) :
    X →ₐ[R] Colimit R Ω where
  __ := (colimit.ι (functor (R := R) (Ω := Ω)) X).right.hom
  commutes' r := by
    exact congr($((colimit.ι (functor (R := R) (Ω := Ω)) X).w).hom r)

/-- The compatible geometric points induce a canonical point of the filtered colimit. -/
noncomputable def colimitPoint : Colimit R Ω →ₐ[R] Ω where
  __ := (colimit.desc (functor (R := R) (Ω := Ω))
    (pointCocone (R := R) (Ω := Ω))).right.hom
  commutes' r := by
    exact congr($((colimit.desc (functor (R := R) (Ω := Ω))
      (pointCocone (R := R) (Ω := Ω))).w).hom r)

@[simp]
theorem colimitPoint_comp_toColimit (X : PointedEtaleNeighborhood R Ω) :
    (colimitPoint (R := R) (Ω := Ω)).comp (toColimit (R := R) (Ω := Ω) X) = X.point := by
  ext x
  exact congr($(colimit.ι_desc (pointCocone (R := R) (Ω := Ω)) X).right.hom x)

variable [IsDomain Ω]

/-- The prime ideal of the filtered colimit selected by its geometric point. -/
noncomputable def colimitPointPrime : Ideal (Colimit R Ω) :=
  RingHom.ker (colimitPoint (R := R) (Ω := Ω)).toRingHom

noncomputable instance : (colimitPointPrime (R := R) (Ω := Ω)).IsPrime :=
  RingHom.ker_isPrime (colimitPoint (R := R) (Ω := Ω)).toRingHom

/-- Elements outside the point prime map to units when the target is a field. -/
theorem colimitPoint_isUnit_of_mem_primeCompl (hΩ : IsField Ω)
    (x : (colimitPointPrime (R := R) (Ω := Ω)).primeCompl) :
    IsUnit (colimitPoint (R := R) (Ω := Ω) x) := by
  have hx : colimitPoint (R := R) (Ω := Ω) x ≠ 0 := by
    intro hzero
    exact (Ideal.mem_primeCompl_iff.mp x.property) (by
      change colimitPoint (R := R) (Ω := Ω) x = 0
      exact hzero)
  obtain ⟨y, hy⟩ := hΩ.mul_inv_cancel hx
  exact IsUnit.of_mul_eq_one y hy

/-- The residue field at the point prime embeds canonically into the chosen geometric field. -/
noncomputable def residuePoint (hΩ : IsField Ω) :
    (colimitPointPrime (R := R) (Ω := Ω)).ResidueField →ₐ[R] Ω :=
  Ideal.ResidueField.liftₐ (colimitPointPrime (R := R) (Ω := Ω))
    (colimitPoint (R := R) (Ω := Ω)) le_rfl <| by
      intro x hx
      exact colimitPoint_isUnit_of_mem_primeCompl (R := R) (Ω := Ω) hΩ ⟨x, hx⟩

/-- The residue-point map is injective. -/
theorem residuePoint_injective (hΩ : IsField Ω) :
    Function.Injective (residuePoint (R := R) (Ω := Ω) hΩ) := by
  let _ : Nontrivial Ω := hΩ.nontrivial
  exact (residuePoint (R := R) (Ω := Ω) hΩ).injective

/-- The local ring obtained by localizing the filtered colimit at its point prime. -/
abbrev LocalColimit (R₁ Ω₁ : Type u) [CommRing R₁] [CommRing Ω₁] [Algebra R₁ Ω₁]
    [IsDomain Ω₁] : Type u :=
  Localization.AtPrime (colimitPointPrime (R := R₁) (Ω := Ω₁))

/-- The localized filtered colimit is a local ring. -/
theorem localColimit_isLocalRing : IsLocalRing (LocalColimit R Ω) := by
  infer_instance

/-- The canonical map from the filtered colimit to its localization at the point. -/
noncomputable def toLocalColimit : Colimit R Ω →+* LocalColimit R Ω :=
  algebraMap (Colimit R Ω) (LocalColimit R Ω)

/-- The canonical map from the original base ring into the localized filtered colimit. -/
noncomputable def baseToLocalColimit : R →+* LocalColimit R Ω :=
  (toLocalColimit (R := R) (Ω := Ω)).comp (algebraMap R (Colimit R Ω))

/-- The geometric point extends canonically to the localized local candidate. -/
noncomputable def localPoint (hΩ : IsField Ω) : LocalColimit R Ω →+* Ω :=
  IsLocalization.lift (M := (colimitPointPrime (R := R) (Ω := Ω)).primeCompl)
    (S := LocalColimit R Ω) (g := (colimitPoint (R := R) (Ω := Ω)).toRingHom)
    (fun x ↦ colimitPoint_isUnit_of_mem_primeCompl (R := R) (Ω := Ω) hΩ x)

@[simp]
theorem localPoint_comp_toLocalColimit (hΩ : IsField Ω) :
    (localPoint (R := R) (Ω := Ω) hΩ).comp (toLocalColimit (R := R) (Ω := Ω)) =
      (colimitPoint (R := R) (Ω := Ω)).toRingHom := by
  ext x
  exact IsLocalization.lift_eq
    (S := LocalColimit R Ω) (P := Ω)
    (g := (colimitPoint (R := R) (Ω := Ω)).toRingHom)
    (fun y ↦ colimitPoint_isUnit_of_mem_primeCompl (R := R) (Ω := Ω) hΩ y) x

end PointedEtaleNeighborhood

end Pcf.Stacks
