/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Dynamics
public import Pcf.Restriction
public import Pcf.Unnormalized
public import Pcf.NormalizationDynamics
public import Pcf.LocalModel
public import Pcf.Noetherian
public import Pcf.Purity
public import Pcf.NonEtaleLocus
public import Pcf.ZariskiNagata
public import Pcf.Ramification
public import Pcf.Abhyankar
public import Pcf.Geometry
public import Pcf.Wiring
public import Pcf.AllTheWayDown
public import Pcf.SpectrumDynamics
public import Pcf.Bounding.Stacks
public import Pcf.Bounding.StandardPiece
public import Pcf.Bounding.LocalStructure
public import Pcf.Bounding.Pieces
public import Pcf.Bounding.Reduced
public import Pcf.Bounding.Chart
public import Pcf.Bounding.FibreProduct
public import Pcf.Bounding.Divisors
public import Pcf.Bounding.LocalChart
public import Pcf.Bounding.SchemeBridge
public import Pcf.Bounding.AffineStalkBridge
public import Pcf.Bounding.SchemeExtraction
public import Pcf.Bounding.RegularLocus
public import Pcf.Bounding.FiniteTypeRegularLocus
public import Pcf.Bounding.SmoothRegularLocal
public import Pcf.Bounding.FiniteTypeSingularLocusClosed
public import Pcf.Bounding.PrincipalQuotientRegular
public import Pcf.Bounding.DivisorFlagCodimension
public import Pcf.Bounding.DivisorLift
public import Pcf.Bounding.PeriodicLift
public import Pcf.Bounding.SchemeWiring
public import Pcf.Bounding.SchemeDynamics
public import Pcf.Bounding.SchemeIteration
public import Pcf.Bounding.NormalizationRamification
public import Pcf.Bounding.NormalizationSchemeBridge
public import Pcf.Bounding.GlobalNormalization
public import Pcf.Bounding.GlobalNormalizationComparison
public import Pcf.Bounding.GlobalNormalizationNormal
public import Pcf.Bounding.GlobalNormalizationFinite
public import Pcf.Bounding.GlobalNormalizationDynamics
public import Pcf.Bounding.NormalizationPcfEquiv
public import Pcf.Bounding.CoverDescent
public import Pcf.Bounding.GlobalNormalizationMorphism
public import Pcf.Bounding.GlobalNormalizationIteration
public import Pcf.Bounding.InvariantDivisorGeometry
public import Pcf.Bounding.AffineSchemeRamification
public import Pcf.Bounding.ReducedFiberBranch
public import Pcf.Bounding.FiniteSingularCorrection
public import Pcf.Bounding.InvariantDivisorStep0Assembly
public import Pcf.Bounding.InvariantDivisorStep0FiniteType
public import Pcf.Bounding.PcfAllTheWayDownScheme
public import Pcf.Bounding.SchemeAllTheWayDown
public import Pcf.Bounding.DimensionTermination
public import Pcf.Bounding.PcfAllTheWayDownCharZero
public import Pcf.Stacks.Abhyankar.EtaleDescentObjects
public import Pcf.Stacks.Abhyankar.EtaleDescentIsomorphism
public import Pcf.Stacks.Purity.LocalFlatness
public import Pcf.Stacks.Purity.FpqcEtaleDescent
public import Pcf.Stacks.Purity.GenericBaseNormalization
public import Pcf.Stacks.Purity.GenericFiberNormalization
public import Pcf.Stacks.Purity.GenericFiberExtension
public import Pcf.Stacks.Purity.Tag0BM9
public import Pcf.Stacks.Purity.FiniteModuleHartogs
public import Pcf.Stacks.Purity.MiracleFlatnessTwo
public import Pcf.Stacks.Purity.FiniteNormalHartogs
public import Pcf.Stacks.Purity.FiniteNormalAlgebraRecovery
public import Pcf.Stacks.Purity.DiscriminantFiber
public import Pcf.Stacks.Purity.HeightOneEtaleBridge
public import Pcf.Palomar.Unconditional
public import Pcf.Stacks.Abhyankar.DVRAbhyankarDivisible
public import Pcf.Stacks.Abhyankar.StrictComponentClassification
public import Pcf.Stacks.Abhyankar.StrictGenericPresentation
public import Pcf.Stacks.Abhyankar.StrictHeightOneTransport
public import Pcf.Stacks.Abhyankar.StrictHeightOneUnramified
public import Pcf.Stacks.Abhyankar.StrictHenselizationCompletionFlat
public import Pcf.Stacks.Abhyankar.StrictHenselizationLocalize
public import Pcf.Stacks.Abhyankar.StrictNormalDecomposition
public import Pcf.Stacks.Abhyankar.StrictNormalizationColimit
public import Pcf.Stacks.Abhyankar.StrictRootComponent
public import Pcf.Stacks.Abhyankar.StrictRootCover
public import Pcf.Stacks.Abhyankar.Tag0EYG
public import Pcf.Stacks.Abhyankar.Tame.Defs
public import Pcf.Stacks.Abhyankar.Tame.RootExponentUnit
public import Pcf.Stacks.Abhyankar.Tame.StrictBaseChangeTame
public import Pcf.Stacks.Abhyankar.Tame.Tag0EYGTame
public import Pcf.Stacks.Abhyankar.Scheme.Tag0EYH
public import Pcf.Stacks.Abhyankar.Scheme.EffectiveCartier
public import Pcf.Stacks.Common.EtaleNormal
public import Pcf.Stacks.Common.RegularLocalization
public import Pcf.Stacks.Common.RegularNormal
public import Pcf.Stacks.Purity.Completion
public import Pcf.Stacks.Purity.CompletionDescent
public import Pcf.Stacks.Purity.RegularPairSections
public import Pcf.Stacks.Purity.FormalEtaleLift
public import Pcf.Stacks.Purity.HenselianFiniteEtaleLift
public import Pcf.Stacks.Purity.HypersurfaceLiftingComplete
public import Pcf.Stacks.Purity.PuncturedEtaleOfPointwise
public import Pcf.Stacks.Purity.Tag0BMA
public import Pcf.Stacks.Purity.Tag0BMB
public import Pcf.Stacks.Purity.Tag0BMBLocalModel
public import Pcf.Stacks.Purity.Tag0BMBScheme
public import Pcf.Stacks.Purity.Tag0BMBSchemeAPI
public import Pcf.Stacks.Purity.GabberPolynomialIdempotent
public import Pcf.Stacks.Abhyankar.DivisorNormalizationTransport
public import Pcf.Stacks.Abhyankar.LocalizedNormalizationComparison
public import Pcf.Stacks.Purity.DiscriminantGlobal
public import Pcf.Stacks.Purity.StandardEtaleSectionLifting
public import Pcf.Stacks.Purity.DimensionTwo
public import Pcf.Stacks.Purity.LocalEtaleSectionLifting
public import Pcf.Stacks.Purity.IntegralIdempotentPolynomial
public import Pcf.Stacks.Purity.OuterInduction
public import Pcf.Stacks.Purity.HypersurfaceLifting
public import Pcf.Stacks.Purity.HenselianIdempotents
public import Pcf.Stacks.Purity.FiniteAlgebraIdempotents
public import Pcf.Stacks.Purity.HenselianGabberPolynomial
public import Pcf.Stacks.Purity.GabberPolynomialSplit
public import Pcf.Stacks.Purity.Tag0BMBAssembly
public import Pcf.Stacks.Purity.Tag0BMAClauses
public import Pcf.Stacks.Purity.Tag0BM9Equivalence
public import Pcf.Stacks.Abhyankar.StrictHenselizationConstruction
public import Pcf.Stacks.Abhyankar.StrictHenselizationResidue
public import Pcf.Stacks.Abhyankar.StrictHenselizationFiniteEtale
public import Pcf.Stacks.Abhyankar.StrictHenselizationStages
public import Pcf.Stacks.Abhyankar.StrictHenselizationHenselian
public import Pcf.Stacks.Abhyankar.StrictHenselizationQuotient
public import Pcf.Stacks.Abhyankar.StrictHenselizationBase
public import Pcf.Stacks.Abhyankar.StrictHenselizationBaseChange
public import Pcf.Stacks.Abhyankar.StrictHenselizationQuotientStandard
public import Pcf.Stacks.Abhyankar.StrictHenselizationQuotientRefinement
public import Pcf.Stacks.Abhyankar.StrictHenselizationQuotientFinality
public import Pcf.Stacks.Abhyankar.StrictHenselizationQuotientComparison
public import Pcf.Stacks.Abhyankar.StrictHenselizationColimitBaseChange
public import Pcf.Stacks.Abhyankar.StrictHenselizationLocalBaseChange
public import Pcf.Stacks.Abhyankar.StrictHenselizationMaximalIdeal
public import Pcf.Stacks.Abhyankar.StrictHenselizationDimension
public import Pcf.Stacks.Abhyankar.StrictHenselizationDomain
public import Pcf.Stacks.Abhyankar.StrictHenselizationNoetherian
public import Pcf.Stacks.Abhyankar.StrictHenselizationColimit
public import Pcf.Stacks.Abhyankar.StrictHenselizationStandardDescent
public import Pcf.Stacks.Abhyankar.StrictHenselizationRegularity
public import Pcf.Stacks.Abhyankar.StandardCoverAddendum
public import Pcf.Stacks.Abhyankar.TameRamification
public import Pcf.Stacks.Abhyankar.StandardCover
public import Pcf.Stacks.Abhyankar.StandardCoverNormalization
public import Pcf.Stacks.Abhyankar.NormalizationBaseChange
public import Pcf.Stacks.Abhyankar.StandardCoverGeometry
public import Pcf.Stacks.Abhyankar.StandardCoverBaseChange
public import Pcf.Stacks.Abhyankar.NormalizationGeometry
public import Pcf.Stacks.Abhyankar.StandardCoverBaseCase
public import Pcf.Stacks.Abhyankar.StandardCoverPresentation
public import Pcf.Stacks.Abhyankar.DVR
public import Pcf.Stacks.Abhyankar.DVRAbhyankar
public import Pcf.Stacks.Abhyankar.DVRKummerBaseChange
public import Pcf.Stacks.Abhyankar.KummerIntermediate
public import Pcf.Stacks.Abhyankar.KummerDVR
public import Pcf.Stacks.Abhyankar.KummerFraction
public import Pcf.Stacks.Abhyankar.KummerFractionEquiv
public import Pcf.Stacks.Abhyankar.KummerClauses
public import Pcf.Stacks.Abhyankar.KummerTame
public import Pcf.Stacks.Abhyankar.KummerRootsOfUnity
public import Pcf.Stacks.Abhyankar.KummerPowers
public import Pcf.Stacks.Abhyankar.KummerNormDescent
public import Pcf.Stacks.Abhyankar.KummerNormalizationAssembly
public import Pcf.Stacks.Abhyankar.KummerIntermediateEquiv
public import Pcf.Stacks.Abhyankar.StrictStandardConclusion
public import Pcf.Stacks.Abhyankar.StrictStandardAssembly
public import Pcf.Stacks.Abhyankar.Tag0EYE
public import Pcf.Stacks.Abhyankar.StrictNormalizationEmbedding
public import Pcf.Stacks.Abhyankar.HeightOneKummerTransport
public import Pcf.Stacks.Abhyankar.DivisorRootLocalization
public import Pcf.Bounding.AffineBridge
public import Pcf.Bounding.Wiring
public import Pcf.Examples.Squaring
public import Pcf.Examples.CharP
public import Pcf.Examples.Cusp
public import Pcf.Examples.CofiniteWitness
public import Pcf.Examples.Pinched

/-!
# Trust audit

`#print axioms` for every headline result of the development, in one place.

**Read `lean/AXIOMS.md` before drawing conclusions from the output below.**
Every line reports only `propext`, `Classical.choice`, `Quot.sound` — the
standard logical axioms of Lean and Mathlib. That is *not* a claim that the
development assumes nothing. The assumed mathematics of the manuscript
(Theorem `thm:bounding`, finiteness of the branch divisor, lying over, and the
scheme-theoretic meaning of "prime" and "ramification index") is carried in
*fields* of `Pcf.DivDyn` and `Pcf.PcfSetup` — that is, in hypotheses — and
hypotheses are invisible to `#print axioms` by construction.

`Pcf.Examples.diagonalSquaring`'s `key` field is proved rather than assumed, so
`Pcf.Examples.diagonalSquaring_res_pcf` witnesses that `Pcf.PcfSetup.res_pcf` is
not vacuous. On the chart route (`Pcf/Bounding/`), `key1` is a theorem derived from
Zariski–Nagata purity and Abhyankar's lemma; see `lean/AXIOMS.md` §G.
-/

@[expose] public section

/-! ## The conjecture the project is named after

Conjecture `conj:pcfawd` of `latex/paper.tex` ("PCF all the way down"), due to the authors and
quoted
on p. 2 of Bridy–Ingram–Jones–Juul–Levy–Manes–Rubinstein-Salzedo–Silverman, *Finite
ramification for preimage fields of post-critically finite morphisms*, Math. Res. Lett.
**24** (2017), 1633–1647, `arXiv:1511.00194`. Both paragraphs are proved here, in the
abstract layer and conditionally; see `Pcf/AllTheWayDown.lean`. -/

#print axioms Pcf.pcf_periodic_prime
#print axioms Pcf.pcf_all_the_way_down
#print axioms Pcf.pcSet_finite_all_the_way_down

/-! ## §`sec:defs`–§`sec:prelim`: divisorial dynamics -/

#print axioms Pcf.DivDyn.IsChain.extend
#print axioms Pcf.DivDyn.exists_isChain_iff
#print axioms Pcf.DivDyn.iterRam_add
#print axioms Pcf.DivDyn.mem_branch_iter_iff
#print axioms Pcf.DivDyn.mem_branch_iter_succ
#print axioms Pcf.DivDyn.pcSet_iter
#print axioms Pcf.DivDyn.pcf_iter_iff
#print axioms Pcf.DivDyn.pcf_iff_forall_orbit_finite
#print axioms Pcf.DivDyn.pcf_of_finite_cover

/-! ## §`sec:main`: Theorem `thm:normal-invariant` and its corollaries -/

#print axioms Pcf.PcfSetup.branch_iter_subset_bound
#print axioms Pcf.PcfSetup.res_pcf
#print axioms Pcf.PcfSetup.res_pcf_of_iter
#print axioms Pcf.PcfSetup.normalization_pcf
#print axioms Pcf.pcf_descent

/-! ## §`sec:bounding` Step 3: the standard tame local model -/

#print axioms Pcf.LocalModel.localPoly_monic
#print axioms Pcf.LocalModel.free
#print axioms Pcf.LocalModel.quotientRootEquiv
#print axioms Pcf.LocalModel.root_mem_nonZeroDivisors

/-! ## §`sec:bounding`: the finiteness engine and Zariski–Nagata purity -/

#print axioms Pcf.IsPrime.not_subset_sUnion
#print axioms Pcf.IsPrime.inter_sUnion_ne_self
#print axioms Pcf.not_subset_of_two_le_codim
#print axioms Pcf.finite_isPrime_subset
#print axioms Pcf.PurityData.notMem_nonEtale_of_specializes
#print axioms Pcf.PurityData.codim_eq_one
#print axioms Pcf.PurityData.finite_isPrime_subset_nonEtale

/-! ## §`sec:bounding`: Theorem `thm:bounding` -/

#print axioms Pcf.Ramification.ramificationIdx_eq_one_of_bijective
#print axioms Pcf.LocalModel.restrictionMap_bijective
#print axioms Pcf.LocalModel.root_ne_zero_mod_algebraMap
#print axioms Pcf.nonempty_unramifiedWitness_iff
#print axioms Pcf.UnramifiedWitness.eq_one
#print axioms Pcf.LocalModel.unramifiedWitness
#print axioms Pcf.Prop41Data.finite_bound
#print axioms Pcf.Prop41Data.finite_sing_subtype
#print axioms Pcf.Prop41Data.finite_meets_subtype

/-! ## §`sec:bounding`→§`sec:main`: the join -/

#print axioms Pcf.UnramifiedWitness.trivial
#print axioms Pcf.divDynOfGeometry
#print axioms Pcf.PcfGeometry.sing_finite
#print axioms Pcf.PcfGeometry.meets_finite
#print axioms Pcf.PcfGeometry.toPcfSetup
#print axioms Pcf.PcfGeometry.res_pcf
#print axioms Pcf.PcfGeometry.res_pcf_of_iter

/-! ## §`sec:bounding`: Theorem `thm:bounding` **derived** from purity and Abhyankar's lemma

`Pcf/Bounding/`. The two classical inputs are the fields `purity` and `abhyankar` of
`Pcf.BoundingChart`, isolated in `Pcf/Stacks/Purity.lean` and
`Pcf/Stacks/Abhyankar.lean` with their exact Stacks tag proof spines;
all three standard facts are proved in the form used here: Tags 033B and 01JT by
`Pcf.Stacks.isReduced_of_etale_of_isDomain` and `Pcf.Stacks.existsPrimeOverBoth`, and the
finite-presentation case of Tag 036W by `Pcf.Stacks.etaleLocalOnSource`. Everything
printed here reports only the standard axioms, as it must: the assumed inputs are
hypotheses. -/

#print axioms Pcf.Stacks.ZariskiNagataPurityInputsAt
#print axioms Pcf.Stacks.HasZariskiNagataPurityAt
#print axioms Pcf.Stacks.ZariskiNagataPurity.of_etale
#print axioms Pcf.Stacks.algebraMap_flat_iff_localRingHom_flat
#print axioms Pcf.Stacks.isRegularLocalRing_quotient_minimalGenerator
#print axioms Pcf.Stacks.ringKrullDim_quotient_minimalGenerator_eq
#print axioms Pcf.Stacks.exists_regularLocalRing_quotient_minimalGenerator
#print axioms Pcf.Stacks.exists_regularLocalRing_quotient_of_ringKrullDim_eq_succ
#print axioms Pcf.Stacks.koszulPairLeft
#print axioms Pcf.Stacks.koszulPairRight
#print axioms Pcf.Stacks.koszulPairTensorEquiv
#print axioms Pcf.Stacks.koszulPairTensorEquiv_tmul
#print axioms Pcf.Stacks.koszulPairTensorEquiv_rTensor_left
#print axioms Pcf.Stacks.lid_rTensor_koszulPairRight
#print axioms Pcf.Stacks.exists_koszul_relation_of_isSMulRegular_pair
#print axioms Pcf.Stacks.exact_koszulPair_of_isSMulRegular
#print axioms Pcf.Stacks.exact_rTensor_koszulPair_of_isSMulRegular
#print axioms
  Pcf.Stacks.range_koszulPairRight_subtype_rTensor_injective_of_isSMulRegular
#print axioms Pcf.Stacks.range_koszulPairRight_eq_span
#print axioms Pcf.Stacks.Module.free_of_regular_pair_generates_maximalIdeal
#print axioms Pcf.Stacks.isWeaklyRegular_pair_of_integral_local_normal
#print axioms
  Pcf.Stacks.Module.free_of_finitePresentation_integral_local_normal_dimension_two
#print axioms Pcf.Stacks.exists_regular_pair_span_maximalIdeal_of_dimension_two
#print axioms
  Pcf.Stacks.Module.free_of_finitePresentation_integral_local_normal_of_dimensions_eq_two
#print axioms
  Pcf.Stacks.isSMulRegular_quotient_of_span_maximalIdeal_of_finite_stacksNormal
#print axioms
  Pcf.Stacks.Module.free_of_finite_torsionFree_stacksNormal_dimension_two
#print axioms Pcf.Stacks.isUnit_of_isUnit_localizationAt_height_one
#print axioms Pcf.Stacks.Algebra.traceMatrix_baseChange
#print axioms Pcf.Stacks.Algebra.discr_baseChange
#print axioms Pcf.Stacks.Algebra.traceForm_nondegenerate_of_algEquiv
#print axioms Pcf.Stacks.Algebra.traceForm_prod_nondegenerate
#print axioms Pcf.Stacks.Algebra.traceForm_pi_nondegenerate
#print axioms Pcf.Stacks.Algebra.traceForm_nondegenerate_of_formallyEtale
#print axioms Pcf.Stacks.Algebra.discr_ne_zero_of_formallyEtale_of_basis
#print axioms Pcf.Stacks.Algebra.discr_ne_zero_of_genericFiber_formallyEtale
#print axioms Pcf.Stacks.Algebra.isUnit_discr_of_etale_of_basis
#print axioms Pcf.Stacks.Algebra.isUnit_map_discr_of_etale_baseChange
#print axioms Pcf.Stacks.Algebra.isReduced_of_discr_ne_zero_of_basis
#print axioms Pcf.Stacks.Algebra.isSeparable_of_isLocalRing_of_discr_ne_zero_of_basis
#print axioms Pcf.Stacks.Algebra.isField_of_isLocalRing_of_discr_ne_zero_of_basis
#print axioms Pcf.Stacks.Algebra.formallyEtale_of_isLocalRing_of_discr_ne_zero_of_basis
#print axioms Pcf.Stacks.Algebra.formallyUnramified_of_isUnit_discr_of_basis
#print axioms Pcf.Stacks.Algebra.etale_of_isUnit_discr_of_basis
#print axioms Pcf.Stacks.Algebra.etale_of_discr_ne_zero_of_isUnit_at_height_one
#print axioms
  Pcf.Stacks.Algebra.etale_of_genericFiber_formallyEtale_of_isUnit_at_height_one
#print axioms Pcf.Stacks.Algebra.etale_of_genericFiber_and_heightOne_baseChange
#print axioms Pcf.Stacks.Ideal.height_under_eq_of_finite_of_flat
#print axioms Pcf.Stacks.heightOneBaseChange_maximal_under_under
#print axioms Pcf.Stacks.Algebra.etale_heightOne_baseChange_of_unramifiedAt_height_one
#print axioms Pcf.Stacks.Algebra.etale_of_genericFiber_and_unramifiedAt_height_one
#print axioms Pcf.Stacks.puncturedHypersurfaceMap
#print axioms Pcf.Stacks.restrictFiniteEtaleToPuncturedHypersurface
#print axioms Pcf.Stacks.PuncturedSpectrumPurity
#print axioms Pcf.Stacks.HypersurfaceFiniteEtaleLifting
#print axioms Pcf.Stacks.puncturedSpectrumPurity_of_hypersurface_lifting
#print axioms Pcf.Stacks.regularLocal_puncturedSpectrumPurity_induction_step
#print axioms Pcf.Stacks.hypersurfaceMap
#print axioms Pcf.Stacks.restrictFiniteEtaleToHypersurface
#print axioms Pcf.Stacks.puncturedHypersurfaceMap_comp_ι
#print axioms Pcf.Stacks.restrictFiniteEtaleToHypersurfaceCompPunctureIso
#print axioms Pcf.Stacks.hypersurfaceFiniteEtaleLifting_of_essSurj_of_fullyFaithful
#print axioms Pcf.Stacks.isIdempotentElem_eq_zero_of_mem_jacobson
#print axioms Pcf.Stacks.eq_of_isIdempotentElem_of_sub_mem_of_le_jacobson
#print axioms Pcf.Stacks.exists_isIdempotentElem_sub_mem_of_henselian
#print axioms Pcf.Stacks.existsUnique_isIdempotentElem_lift_of_henselian
#print axioms Pcf.Stacks.bijective_idempotentQuotientMap_of_henselian
#print axioms Pcf.Stacks.map_le_jacobson_bot_of_le_jacobson_of_isIntegral
#print axioms Pcf.Stacks.injective_idempotentQuotientMap_of_isIntegral
#print axioms Pcf.Stacks.injective_idempotentQuotientMap_of_finite_henselian
#print axioms Pcf.Stacks.exists_root_sub_one_mem_of_map_eq_X_pow_mul_X_sub_one
#print axioms Pcf.Stacks.eq_of_isRoot_of_sub_one_mem_of_map_eq_X_pow_mul_X_sub_one
#print axioms Pcf.Stacks.existsUnique_root_sub_one_mem_of_map_eq_X_pow_mul_X_sub_one
#print axioms Pcf.Stacks.exists_coprime_factorization_of_map_eq_X_pow_mul_X_sub_one
#print axioms Pcf.Stacks.FiniteNormalPuncturedEtalePurity
#print axioms Pcf.Stacks.ZariskiNagataFiniteLocalModel
#print axioms Pcf.Stacks.exists_tag0BMB_finiteComponent
#print axioms Pcf.Stacks.hasZariskiNagataPurityAt_of_finiteLocalModel
#print axioms Pcf.Stacks.zariskiNagataPurity_of_finiteLocalModels
#print axioms Pcf.Stacks.finiteEtaleCover_sections_finite_etale
#print axioms Pcf.Stacks.finiteEtaleCover_algGamma_unit_isIso
#print axioms Pcf.Stacks.puncturedSectionsSpecAdjunction_counit_isIso_of_bijective
#print axioms Pcf.Stacks.finiteEtaleAlgebra_exists_regularPair
#print axioms Pcf.Stacks.etale_puncturedRestriction_of_etale
#print axioms Pcf.Stacks.finiteEtaleAlgebra_openSections_bijective
#print axioms Pcf.Stacks.finiteEtaleAlgebra_pullbackSections_bijective
#print axioms Pcf.Stacks.finiteEtaleAlgebra_puncturedSectionsSpecAdjunction_counit_isIso
#print axioms Pcf.Stacks.finiteNormalPuncturedEtalePurity_of_puncturedSpectrumPurity
#print axioms Pcf.Stacks.spec_algebraMap_res
#print axioms Pcf.Stacks.openSections_algebraMap_surjective_of_module_regularPair
#print axioms Pcf.Stacks.openSections_algebraMap_bijective_of_module_regularPair
#print axioms Pcf.Stacks.finiteNormalAlgebra_openSections_bijective
#print axioms Pcf.Stacks.puncturedSectionsSpecAdjunction
#print axioms
  Pcf.Stacks.finiteNormalPuncturedEtaleAlgebraProperty_isClosedUnderIsomorphisms
#print axioms Pcf.Stacks.finiteNormalAlgebra_pullbackSections_bijective
#print axioms Pcf.Stacks.puncturedSectionsSpecAdjunction_counit_isIso
#print axioms
  Pcf.Stacks.puncturedGlobalSections_finiteNormalPuncturedEtaleAlgebraProperty
#print axioms Pcf.Stacks.tag0BM9Adjunction
#print axioms Pcf.Stacks.tag0BM9Adjunction_counit_isIso
#print axioms Pcf.Stacks.finiteNormalAlgebraToPuncturedCover_fullyFaithful
#print axioms Pcf.Stacks.finiteNormalAlgebraToPuncturedCover_essSurj
#print axioms Pcf.Stacks.tag0BM9Equivalence
#print axioms Pcf.Stacks.tag0BM9_puncturedCoverRecoveryIso
#print axioms Pcf.Stacks.tag0BM9_finiteNormalAlgebraRecoveryIso
#print axioms Pcf.Stacks.tag0BM9_puncturedGlobalSections_fullyFaithful
#print axioms Pcf.Stacks.minimalPrime_under_eq_bot_of_isTorsionFree
#print axioms Pcf.Stacks.two_le_height_of_liesOver_of_finite_torsionFree
#print axioms Pcf.Stacks.exists_associatedPrime_liesOver_closedPoint
#print axioms Pcf.Stacks.localized_span_singleton_eq_smul_top
#print axioms Pcf.Stacks.principalQuotient_avoid_closedPoint_of_finite_stacksNormal
#print axioms Pcf.Stacks.exists_isSMulRegular_quotient_mem_maximalIdeal_of_finite
#print axioms Pcf.Stacks.exists_module_regular_pair_of_finite_stacksNormal
#print axioms Pcf.Stacks.exists_module_permutable_regular_pair_of_finite_stacksNormal
#print axioms Pcf.Stacks.exists_eq_pow_smul_of_regular_pair
#print axioms Pcf.Stacks.exists_common_value_of_module_regular_pair
#print axioms Pcf.Stacks.etale_of_fpqc_pullback
#print axioms Pcf.Stacks.formallyEtale_of_flat_of_formallyUnramified_of_isLocalization
#print axioms Pcf.Stacks.isDiscreteValuationRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one
#print axioms Pcf.Stacks.hasZariskiNagataPurityAt_of_height_eq_one
#print axioms Pcf.Stacks.exists_etale_finite_component_of_quasiFiniteAt
#print axioms Pcf.Stacks.mem_puncturedSpectrum_iff
#print axioms Pcf.Stacks.closedPoint_not_mem_puncturedSpectrum
#print axioms Pcf.Stacks.puncturedFiniteEtaleRecovery
#print axioms Pcf.Stacks.puncturedFiniteEtaleExtensionCover
#print axioms Pcf.Stacks.puncturedFiniteEtaleRecoveryIso
#print axioms Pcf.Stacks.restrictFiniteEtaleToPuncturedSpectrum_essSurj
#print axioms Pcf.Stacks.PuncturedFiniteEtaleMorphismsExtend
#print axioms Pcf.Stacks.restrictFiniteEtaleToPuncturedSpectrum_fullyFaithful
#print axioms Pcf.Stacks.restrictFiniteEtaleToPuncturedSpectrumEquivalence
#print axioms Pcf.Stacks.IsStacksNormalRing
#print axioms Pcf.Stacks.IsStacksNormalRing.isReduced
#print axioms Pcf.Stacks.IsStacksNormalRing.pi
#print axioms Pcf.Stacks.finiteNormalPuncturedEtaleAlgebraProperty
#print axioms Pcf.Stacks.FiniteNormalPuncturedEtaleAlgebra.isFinite_algSpec
#print axioms Pcf.Stacks.finiteNormalAlgebraToPuncturedCover
#print axioms Pcf.Stacks.puncturedCoverRecoveryIso
#print axioms Pcf.Stacks.PuncturedGlobalSectionsMorphismsExtend
#print axioms Pcf.Stacks.tag0BM9EquivalenceOfMorphismExtension
#print axioms Pcf.Stacks.tag0BM9EquivalenceOfRecovery
#print axioms Pcf.Stacks.IsIntegralClosure.isDomain_of_isIntegralClosureInField
#print axioms Pcf.Stacks.IsIntegralClosure.isIntegrallyClosed_of_finiteExtension
#print axioms Pcf.Stacks.IsIntegralClosure.isStacksNormalRing_of_finiteExtension
#print axioms Pcf.Stacks.IsIntegralClosure.moduleFinite_of_finiteSeparableExtension
#print axioms Pcf.Stacks.isCompact_puncturedSpectrum
#print axioms Pcf.Stacks.puncturedSpectrum_nonempty_of_one_le_ringKrullDim
#print axioms Pcf.Stacks.puncturedSpectrum_restriction_injective
#print axioms Pcf.Stacks.exists_nonzero_mem_maximalIdeal_of_one_le_ringKrullDim
#print axioms Pcf.Stacks.exists_regularSequence_one_of_one_le_ringKrullDim
#print axioms Pcf.Stacks.PrincipalQuotientsAvoidClosedPoint
#print axioms Pcf.Stacks.maximalIdeal_not_mem_associatedPrimes_iff_exists_isSMulRegular_quotient
#print axioms Pcf.Stacks.exists_regularSequence_two_of_principalQuotient_not_associated
#print axioms Pcf.Stacks.maximalIdeal_not_isPrincipal_of_two_le_ringKrullDim
#print axioms Pcf.Stacks.principalQuotientsAvoidClosedPoint_of_two_le_ringKrullDim
#print axioms Pcf.Stacks.exists_regularSequence_two_of_isIntegrallyClosed
#print axioms Pcf.Stacks.pow_dvd_of_isSMulRegular_quotient
#print axioms Pcf.Stacks.exists_common_value_of_regular_pair
#print axioms Pcf.Stacks.fraction_of_regular_pair_eq_algebraMap
#print axioms Pcf.Stacks.exists_fraction_intersection_pair_of_isIntegrallyClosed
#print axioms Pcf.Stacks.basicOpen_germ_fraction
#print axioms Pcf.Stacks.puncturedSpectrum_algebraMap_surjective
#print axioms Pcf.Stacks.puncturedSpectrum_restriction_surjective
#print axioms Pcf.Stacks.puncturedSpectrum_restriction_bijective
#print axioms Pcf.Stacks.isIso_puncturedSpectrum_algebraMap
#print axioms Pcf.Stacks.genericFiber_isArtinian
#print axioms Pcf.Stacks.genericFiber_maximalSpectrum_finite
#print axioms Pcf.Stacks.genericFiber_component_isField
#print axioms Pcf.Stacks.genericFiber_isReduced
#print axioms Pcf.Stacks.genericFiber_equivPi
#print axioms Pcf.Stacks.genericPoint_mem_puncturedSpectrum
#print axioms Pcf.Stacks.puncturedCoverGenericFiber_isAffine
#print axioms Pcf.Stacks.puncturedCoverGenericFiber_finite_appTop
#print axioms Pcf.Stacks.puncturedCoverGenericFiber_etale_appTop
#print axioms Pcf.Stacks.puncturedCoverGenericFiber_ringHom_finite
#print axioms Pcf.Stacks.puncturedCoverGenericFiber_ringHom_etale
#print axioms Pcf.Stacks.puncturedCoverGenericFiber_exists_separableFields
#print axioms Pcf.Stacks.puncturedCover_sections_isReduced
#print axioms Pcf.Stacks.genericPoint_sections_isIntegrallyClosedIn
#print axioms Pcf.Stacks.genericPoint_fromNormalization_isIso
#print axioms Pcf.Stacks.puncturedCover_genericFiber_fromNormalization_isIso
#print axioms Pcf.Stacks.puncturedCover_affineSections_isIntegrallyClosedInGeneric
#print axioms Pcf.Stacks.normalizationDesc_isIso_of_fromNormalization_isIso
#print axioms Pcf.Stacks.normalizationIsoOfSourceIso
#print axioms Pcf.Stacks.normalizationRestrictIsoOfOpenImmersion
#print axioms Pcf.Stacks.puncturedCover_genericFiber_normalizationDesc_isIso
#print axioms Pcf.Stacks.puncturedCover_genericFiber_normalizationRestrictIso
#print axioms Pcf.Stacks.puncturedCover_baseGenericPullback_algebraEtale
#print axioms Pcf.Stacks.puncturedCover_baseGenericPullback_algebraMap
#print axioms
  Pcf.Stacks.puncturedCover_genericFiber_normalizationSections_isStacksNormalRing
#print axioms Pcf.Stacks.puncturedCover_genericFiber_normalizationIntegralClosure_finite
#print axioms Pcf.Stacks.puncturedCover_genericFiber_fromNormalization_finite_appTop
#print axioms Pcf.Stacks.puncturedCover_genericFiber_normalizationSections_finite
#print axioms Pcf.Stacks.puncturedCover_genericFiber_normalization_isFinite
#print axioms Pcf.Stacks.puncturedCover_genericFiber_normalizationSpecMap
#print axioms Pcf.Stacks.puncturedCover_genericFiber_normalizationSpecRestrictIso
#print axioms Pcf.Stacks.normalizationIsoOfSourceIsoEq
#print axioms Pcf.Stacks.normalizationIsoOfSourceIsoEq_hom_fromNormalization
#print axioms Pcf.Stacks.normalizationRestrictOverIsoOfOpenImmersion
#print axioms Pcf.Stacks.puncturedCover_genericFiber_normalizationSpecRestrictOverIso
#print axioms
  Pcf.Stacks.puncturedCover_genericFiber_normalizationSections_isTorsionFree
#print axioms Pcf.Stacks.puncturedCover_exists_finiteNormalPuncturedEtaleAlgebra
#print axioms Pcf.Stacks.puncturedCover_exists_finiteNormalExtension
#print axioms Pcf.Stacks.finiteNormalModel_moduleFinite
#print axioms Pcf.Stacks.finiteNormalModel_isStacksNormalRing
#print axioms Pcf.Stacks.IsStacksNormalRing.of_ringEquiv
#print axioms Pcf.Stacks.integralClosure_ringEquiv_of_baseRingEquiv
#print axioms Pcf.Stacks.integralClosure_isStacksNormalRing_of_baseRingEquiv
#print axioms Pcf.Stacks.finiteSeparableProduct_integralClosure_equiv
#print axioms Pcf.Stacks.finiteSeparableProduct_integralClosure_isStacksNormalRing
#print axioms Pcf.Stacks.finiteEtaleAlgebra_integralClosure_isStacksNormalRing
#print axioms Pcf.Stacks.finiteEtaleAlgebra_integralClosure_finite
#print axioms Pcf.Stacks.integralClosure_finite_of_baseRingEquiv
#print axioms Pcf.Stacks.puncturedCoverGenericFiber_integralClosure_isStacksNormalRing
#print axioms Pcf.Stacks.finiteNormalModel_genericFiberEquiv
#print axioms Pcf.Stacks.finiteSeparableProduct_integralClosure_finite
#print axioms Pcf.Stacks.puncturedCover_exists_finiteNormalGenericModel
#print axioms Pcf.Stacks.puncturedCover_exists_finiteNormalGenericSchemeModel
#print axioms Pcf.Stacks.puncturedCoverGenericFiber_integralClosure_finite
#print axioms Pcf.Stacks.puncturedCover_sections_integralClosure_finite
#print axioms Pcf.Stacks.puncturedCover_isNoetherian
#print axioms Pcf.Stacks.genericPoint_fromSpecStalk_flat
#print axioms Pcf.Stacks.genericPoint_fromSpecStalk_dominant
#print axioms Pcf.Stacks.genericPoint_toPuncturedSpectrum_schemeTheoreticallyDominant
#print axioms Pcf.Stacks.genericPoint_toPuncturedSpectrum_quasiCompact
#print axioms Pcf.Stacks.puncturedCover_genericBaseChange_isIso
#print axioms Pcf.Stacks.puncturedCoverGenericFiber_iso_basePullback
#print axioms Pcf.Stacks.puncturedCover_genericPullback_sections_injective
#print axioms Pcf.Stacks.puncturedCoverGenericFiber_sectionMap
#print axioms Pcf.Stacks.puncturedCoverGenericFiber_sectionMap_injective
#print axioms Pcf.Stacks.puncturedCoverGenericFiber_sectionMap_base
#print axioms Pcf.Stacks.puncturedCoverGenericFiber_sectionAlgHom
#print axioms Pcf.Stacks.puncturedCoverGenericFiber_sectionAlgHom_injective
#print axioms Pcf.Stacks.puncturedCover_normalization_isAffine
#print axioms Pcf.Stacks.puncturedCover_normalizationSpecMap
#print axioms Pcf.Stacks.puncturedCover_normalizationRestrictIso
#print axioms Pcf.Stacks.puncturedCover_normalizationSpecRestrictIso
#print axioms Pcf.Stacks.puncturedCover_normalizationSectionsIso
#print axioms Pcf.Stacks.puncturedCover_normalizationIntegralClosure_finite
#print axioms Pcf.Stacks.puncturedCover_normalizationSections_isReduced
#print axioms Pcf.Stacks.puncturedCover_normalization_isReduced
#print axioms Pcf.Stacks.puncturedCover_normalization_finite_appTop
#print axioms Pcf.Stacks.puncturedCover_normalizationSections_finite
#print axioms Pcf.Stacks.puncturedCover_normalization_isFinite
#print axioms Pcf.Stacks.EtaleDescent.exists_stage_containing_finite_set
#print axioms Pcf.Stacks.EtaleDescent.exists_finitePresentation_model_of_isColimit
#print axioms Pcf.Stacks.EtaleDescent.exists_common_factorizations_of_finitePresentation
#print axioms Pcf.Stacks.EtaleDescent.exists_common_stage_for_two_eventual_eq_of_finitePresentation
#print axioms Pcf.Stacks.EtaleDescent.ringCoconeAboveIsColimit
#print axioms Pcf.Stacks.EtaleDescent.baseChangeCoconeIsColimit
#print axioms Pcf.Stacks.EtaleDescent.exists_descendedMapPair
#print axioms Pcf.Stacks.EtaleDescent.exists_descendedAlgEquiv
#print axioms Pcf.Stacks.EtaleDescent.exists_descendedAlgEquiv_of_standardTameCover
#print axioms Pcf.Stacks.EtaleDescent.exists_descendedAlgEquiv_of_standardTameCovers
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.exists_stage_units
#print axioms
  Pcf.Stacks.EtaleDescent.StageAlgebra.EquivalenceDescent.exists_stage_standardTameCover_of_limit_equiv
#print axioms Pcf.Stacks.isRegularLocalRing_of_flat_of_formallyUnramified
#print axioms Pcf.Stacks.isRegularRing_of_etale
#print axioms Pcf.Stacks.quotient_span_isRegularRing_of_etale
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.presentationModelEquiv
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.exists_common_refinement
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.exists_equalizing_refinement
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.colimitPoint_comp_toColimit
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.residuePoint_injective
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimit_isLocalRing
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localPoint_comp_toLocalColimit
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.exists_pointedEtaleNeighborhood_point_eq
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.residuePoint_surjective
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.residuePoint_bijective
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.residueFieldAlgEquiv
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.residueField_isSepClosed
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.bijective_algebraMap_finiteEtale_local
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.finiteEtaleLocalAlgEquiv
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.exists_stage_of_colimit_element
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.exists_stage_containing_finite_colimit_set
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.exists_stage_of_localColimit_element
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.exists_stage_containing_finite_localColimit_set
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.residueFieldAlgEquiv_residue_toLocalColimitAlgHom
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.exists_stage_polynomial_with_simple_point
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.exists_root_refinement
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.exists_root_lifting_simple_residue_root
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimit_henselianLocalRing
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimit_strictlyHenselianLocalRing
#print axioms Pcf.Stacks.HenselianLocalRing.quotient_of_le_maximalIdeal
#print axioms Pcf.Stacks.residueFieldMap_bijective_of_surjective
#print axioms Pcf.Stacks.isSepClosed_of_ringEquiv
#print axioms Pcf.Stacks.StrictlyHenselianLocalRing.quotient_of_le_maximalIdeal
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimit_base_isLocalHom
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.map_le_maximalIdeal_localColimit
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.quotient_localColimit_strictlyHenselianLocalRing
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.baseChange
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.quotientStageEquiv
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.quotientBaseChange
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.quotientStagePoint_mk
#print axioms Pcf.Stacks.QuotientStandardEtale.liftPair
#print axioms Pcf.Stacks.QuotientStandardEtale.baseChangeEquiv
#print axioms Pcf.Stacks.QuotientStandardEtale.tensorBaseChangeEquiv
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.exists_quotientBaseChange_refinement
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.exists_quotientBaseChange_equalizing_refinement
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.quotientBaseChange_final
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.exists_baseChange_refinement_of_toColimit_eq
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.colimitQuotientBaseChangeAlgHom_surjective
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.colimitQuotientBaseChangeAlgHom_injective
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.colimitQuotientBaseChangeAlgHom_bijective
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.colimitBaseChangeRingHom
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.colimitBaseChangeRingHom_toColimit
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.colimitQuotientBaseChangeAlgHom
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.colimitQuotientBaseChangeAlgHom_mk
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimitBaseChangeRingHom
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimitBaseChangeRingHom_toLocalColimit
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localQuotientBaseChangeAlgHom
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localQuotientBaseChangeAlgHom_mk
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.ker_quotientLocalColimitBaseChangeRingHom
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localQuotientBaseChangeAlgHom_surjective
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localQuotientBaseChangeAlgHom_injective
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localQuotientBaseChangeAlgHom_bijective
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localQuotientBaseChangeAlgEquiv
#print axioms Pcf.Stacks.IsRegularLocalRing.of_map_maximalIdeal_eq_of_ringKrullDim_eq
#print axioms
  Pcf.Stacks.PointedEtaleNeighborhood.localColimit_isRegularLocalRing_of_maximalIdeal_eq_of_ringKrullDim_eq
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.point_ker_under
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.map_maximalIdeal_localColimit
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.exists_refinement_eq_zero_of_toLocalColimitAlgHom_eq_zero
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimit_flat
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimit_faithfullyFlat
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.ringKrullDim_localColimit
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.toLocalColimitAlgHom_injective_of_isDomain
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimit_isDomain
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimit_isRegularLocalRing_of_isNoetherianRing
#print axioms Pcf.Stacks.flatModule_free_of_isNilpotent_maximalIdeal
#print axioms Pcf.Stacks.exists_basis_of_flat_of_isNilpotent_maximalIdeal
#print axioms Pcf.Stacks.IsLocalRing.ResidueField.map_bijective_of_surjective
#print axioms Pcf.Stacks.IsLocalRing.ResidueField.mapEquivOfSurjective
#print axioms Pcf.Stacks.Module.Basis.mapSemilinear
#print axioms Pcf.Stacks.Module.Basis.mapSemilinear_apply
#print axioms Pcf.Stacks.residueTensorEquivOfMapMaximalIdeal
#print axioms Pcf.Stacks.residueTensorEquivOfMapMaximalIdeal_tmul
#print axioms Pcf.Stacks.Finsupp.quotientSMulTopEquiv
#print axioms Pcf.Stacks.Finsupp.quotientSMulTopEquiv_mk
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimitQuotientSMulTopEquiv
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimitQuotientSMulTopEquiv_mk
#print axioms
  Pcf.Stacks.PointedEtaleNeighborhood.exists_localColimit_basis_quotient_maximalIdeal_powers
#print axioms
  Pcf.Stacks.PointedEtaleNeighborhood.exists_localColimit_linearCombination_reduceModIdeal_bijective
#print axioms
  Pcf.Stacks.PointedEtaleNeighborhood.exists_localColimit_adicCompletion_map_bijective
#print axioms Pcf.Stacks.flat_quotient_map
#print axioms Pcf.Stacks.flat_pi_self_of_isNoetherianRing
#print axioms Pcf.Stacks.Module.Flat.pi_of_isNoetherianRing
#print axioms Pcf.Stacks.Module.Flat.of_forall_ideal_lTensor_injective
#print axioms Pcf.Stacks.AdicCompletion.map_exact_of_pow_inf_eq_pow_smul
#print axioms Pcf.Stacks.AdicCompletion.map_injective_of_pow_inf_eq_pow_smul
#print axioms Pcf.Stacks.AdicCompletion.mapRange_exact_of_finite
#print axioms Pcf.Stacks.AdicCompletion.mapRange_injective_of_finite
#print axioms Pcf.Stacks.AdicCompletion.exists_mapRange_ker_preimage_of_finite
#print axioms Pcf.Stacks.AdicCompletion.finsupp_flat_of_isNoetherian
#print axioms Pcf.Stacks.Finsupp.finsuppPiLEquiv
#print axioms Pcf.Stacks.Finsupp.finsuppPiLEquiv_apply
#print axioms Pcf.Stacks.Finsupp.ideal_smul_submodule
#print axioms Pcf.Stacks.Finsupp.submodule_inf
#print axioms Pcf.Stacks.Finsupp.exists_pow_inf_eq_pow_smul_submodule
#print axioms Pcf.Stacks.AdicCompletion.finsuppToPi
#print axioms Pcf.Stacks.AdicCompletion.finsuppToPi_apply
#print axioms Pcf.Stacks.AdicCompletion.finsuppToPi_injective
#print axioms Pcf.Stacks.AdicCompletion.pi_flat_of_isNoetherian
#print axioms Pcf.Stacks.AdicCompletion.finsuppToPiRestrictScalars
#print axioms Pcf.Stacks.Module.Flat.lTensor_ideal_injective_of_injective
#print axioms Pcf.Stacks.AdicCompletion.finsuppToPiRestrictScalars_lTensor_injective
#print axioms Pcf.Stacks.AdicCompletion.finsupp_flat_of_forall_ideal_lTensor_injective
#print axioms Pcf.Stacks.free_quotient_maximalIdeal_pow_of_flat
#print axioms Pcf.Stacks.AdicCompletion.map_injective_of_reduceModIdeal
#print axioms Pcf.Stacks.AdicCompletion.map_bijective_of_reduceModIdeal
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimit_quotient_maximalIdeal_pow_free
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.colimitPointPrime_primeCompl_le_isUnit
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.colimitToLocalColimitAlgEquiv
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localCocone
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.colimitCoconeIsoLocalCocone
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localCoconeIsColimit
#print axioms Pcf.Stacks.isNoetherianRing_of_maximalAdicCompletion
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimit_isNoetherianRing_of_completion
#print axioms
  Pcf.Stacks.PointedEtaleNeighborhood.localColimit_isRegularLocalRing_of_completion_flat
#print axioms Pcf.Stacks.isTamelyRamifiedAt_of_all_nat_isUnit
#print axioms Pcf.Stacks.isTamelyRamifiedInCodimensionOneAlong_of_all_nat_isUnit
#print axioms Pcf.Stacks.baseChange_tameInCodimensionOneAlong_of_all_nat_isUnit
#print axioms Pcf.Stacks.localizedStandardPoly_eq_kummerPoly
#print axioms Pcf.Stacks.localizedStandardCover_etale
#print axioms Pcf.Stacks.standardCover_finite
#print axioms Pcf.Stacks.standardCover_free
#print axioms Pcf.Stacks.standardCover_finrank
#print axioms Pcf.Stacks.standardCover_tameInCodimensionOne_charZero
#print axioms Pcf.Stacks.IsFiniteDisjointUnionOfStandardTameCovers.finitePresentation
#print axioms Pcf.Stacks.standardCover_rootQuotient_isRegularRing
#print axioms Pcf.Stacks.standardCover_finite_free_cartier_regular
#print axioms Pcf.Stacks.isIntegrallyClosedIn_away_of_span_isRadical
#print axioms Pcf.Stacks.isReduced_of_isRegularRing
#print axioms Pcf.Stacks.standardCover_isLocalizationAway_root
#print axioms Pcf.Stacks.standardCover_isIntegrallyClosedIn_localizationAway
#print axioms Pcf.Stacks.standardCover_isIntegralClosure_localizationAway
#print axioms Pcf.Stacks.standardCover_isIntegralClosure_localizationAway_of_regular
#print axioms Pcf.Stacks.standardCoverLocalizationEquiv
#print axioms Pcf.Stacks.standardCoversLocalizationEquiv
#print axioms Pcf.Stacks.isIntegralClosure_pi_of_fintype
#print axioms Pcf.Stacks.standardCovers_isIntegralClosure_localizationsAway_of_regular
#print axioms Pcf.Stacks.normalizationEquivStandardCoversOfGenericEquiv
#print axioms Pcf.Stacks.algebraMap_normalizationEquivStandardCoversOfGenericEquiv
#print axioms Pcf.Stacks.normalizationEquivStandardCoversOfLocalizedPresentation
#print axioms Pcf.Stacks.algebraMap_normalizationEquivStandardCoversOfLocalizedPresentation
#print axioms Pcf.Stacks.dvrRootFractionPowerEquiv
#print axioms Pcf.Stacks.isFiniteDisjointUnionOfStandardTameCovers_of_localizedPresentation
#print axioms Pcf.Stacks.strictStandardPresentation_of_localizedPresentation
#print axioms
  Pcf.Stacks.PointedEtaleNeighborhood.hasAbhyankarStandardCoverAt_of_strict_localizedPresentation
#print axioms Pcf.Stacks.Algebra.isEtaleAt_of_zariskiNagataPurity_finite_normal_domain
#print axioms Pcf.Stacks.Algebra.etale_of_zariskiNagataPurity_finite_normal_domain
#print axioms
  Pcf.Stacks.Algebra.etale_across_nonZeroDivisor_of_zariskiNagataPurity_finite_normal_domain
#print axioms Pcf.Stacks.isRegularLocalRing_atPrime_of_regular_principal_quotient
#print axioms Pcf.Stacks.Algebra.tag0EYE_of_zariskiNagataPurity_finite_normal_domain
#print axioms Pcf.Stacks.Algebra.tag0EYE_standardRoot_of_zariskiNagataPurity
#print axioms Pcf.Stacks.fractionRingAlgEquivOfFiniteEtaleLocal
#print axioms Pcf.Stacks.fractionRingAlgEquivOfFiniteEtaleLocalOverFraction
#print axioms Pcf.Stacks.normalIntegralAlgEquivOfFractionRingEquiv
#print axioms Pcf.Stacks.exists_fractionFieldEmbedding_of_tag0EYE_strict_local_normalization
#print axioms Pcf.Stacks.exists_dvrRootFractionPowerEquiv_of_strict_local_normalization
#print axioms Pcf.Stacks.formallyUnramified_of_isUnramifiedAt_maximalIdeal
#print axioms Pcf.Stacks.isUnramifiedAt_of_etale_localizationAway
#print axioms
  Pcf.Stacks.isUnramifiedAt_of_standardRoot_dvrRootPuncturedNormalization_of_root_mem
#print axioms Pcf.Stacks.standardRootTensorAtPrimeEquivDVRRoot
#print axioms Pcf.Stacks.standardRootTensorAtPrimeEquivDVRRoot_root
#print axioms Pcf.Stacks.standardRoot_dvrRoot_isLocalizationAtDivisorPrime
#print axioms Pcf.Stacks.normalizationBaseChangeAlgebra
#print axioms Pcf.Stacks.smoothBaseChangeIntegralClosureEquiv
#print axioms Pcf.Stacks.smoothBaseChangeIntegralClosureEquiv_val
#print axioms Pcf.Stacks.smoothBaseChange_isIntegralClosure
#print axioms Pcf.Stacks.smoothBaseChange_isIntegralClosure_localizationAway
#print axioms Pcf.Stacks.radical_pi_of_finite
#print axioms Pcf.Stacks.quotientPiRingEquiv
#print axioms Pcf.Stacks.isRegularRing_pi_of_finite
#print axioms Pcf.Stacks.standardCoversReducedDivisorIdeal
#print axioms Pcf.Stacks.standardCovers_radical_span_algebraMap_eq_reducedDivisorIdeal
#print axioms Pcf.Stacks.standardCovers_finite
#print axioms Pcf.Stacks.standardCovers_free
#print axioms Pcf.Stacks.standardCoverBaseChangeEquiv
#print axioms Pcf.Stacks.standardCoversBaseChangeEquiv
#print axioms Pcf.Stacks.standardCoversBaseChangeEquivOfUnitEq
#print axioms Pcf.Stacks.IsFiniteDisjointUnionOfStandardTameCovers.baseChange
#print axioms Pcf.Stacks.standardCoversReducedDivisorQuotientEquiv
#print axioms Pcf.Stacks.standardCoversReducedDivisor_isRegularRing
#print axioms Pcf.Stacks.normalizationOfLocalizedPresentation_finite
#print axioms Pcf.Stacks.normalizationOfLocalizedPresentation_free
#print axioms Pcf.Stacks.normalizationReducedDivisorIdealOfLocalizedPresentation
#print axioms Pcf.Stacks.normalization_radical_span_algebraMap_eq_reducedDivisorIdeal
#print axioms Pcf.Stacks.normalizationReducedDivisorQuotientEquiv
#print axioms Pcf.Stacks.normalizationReducedDivisor_isRegularRing
#print axioms Pcf.Stacks.isRegularLocalRing_quotient_localization
#print axioms Pcf.Stacks.standardCover_isRegularLocalRing_atPrime_over_divisor
#print axioms Pcf.Stacks.standardCover_isFiniteDisjointUnionOfStandardTameCovers
#print axioms Pcf.Stacks.IsFiniteDisjointUnionOfStandardTameCovers.selfBaseChange
#print axioms Pcf.Stacks.hasAbhyankarStandardCoverAt_of_standard
#print axioms Pcf.Stacks.hasAbhyankarStandardCoverAt_standardCover
#print axioms Pcf.Stacks.ramificationIdx_over_intermediate_eq_one_of_total_eq
#print axioms Pcf.Stacks.isUnramifiedAt_of_ramificationIdx_total_eq_intermediate_at
#print axioms Pcf.Stacks.hasSeparableResidueFieldsAt_comp_formallyUnramified
#print axioms Pcf.Stacks.isUnramifiedAt_of_ramificationIdx_total_eq_intermediate
#print axioms Pcf.Stacks.etale_of_isEtaleAt_maximalIdeal
#print axioms Pcf.Stacks.isEtaleAt_of_ramificationIdx_total_eq_intermediate
#print axioms Pcf.Stacks.etale_of_dvr_ramificationIdx_total_eq
#print axioms Pcf.Stacks.etale_of_dvr_ramification_square
#print axioms Pcf.Stacks.isUnramifiedAt_of_local_ramification_square
#print axioms Pcf.Stacks.etale_of_equiv_localization_kummerUnit
#print axioms Pcf.Stacks.isUnramifiedAt_of_kummerUnit_local_ramification_square
#print axioms Pcf.Stacks.isUnramifiedAt_of_standardRoot_kummerUnit_local_square
#print axioms
  Pcf.Stacks.isUnramifiedAt_of_standardRoot_integralClosure_kummerUnit_localFactor
#print axioms Pcf.Stacks.kummerUnit_isIntegralClosure_localizationAway_uniformizer
#print axioms Pcf.Stacks.kummerUnit_localizationAtPrime_isRegularLocalRing
#print axioms Pcf.Stacks.kummerUnit_localizationAtPrime_isDomain
#print axioms Pcf.Stacks.kummerUnit_localizationAtPrime_isDiscreteValuationRing
#print axioms Pcf.Stacks.maximalIdeal_under_eq_of_isIntegralClosure
#print axioms Pcf.Stacks.exists_unit_mul_pow_eq_of_ramificationIdx_eq
#print axioms Pcf.Stacks.dvrRootToKummerNormalization
#print axioms Pcf.Stacks.DVRRootPuncturedNormalization
#print axioms Pcf.Stacks.dvrRootPuncturedNormalizationAlgebra
#print axioms Pcf.Stacks.dvrRootPuncturedNormalization_isScalarTower
#print axioms Pcf.Stacks.dvrRootPuncturedNormalization_isIntegralClosure
#print axioms
  Pcf.Stacks.isUnramifiedAt_of_standardRoot_dvrRootPuncturedNormalization_localFactor
#print axioms Pcf.Stacks.DVRRootPuncturedBaseChange
#print axioms Pcf.Stacks.dvrRootPuncturedBaseChangeEquivKummerLocalization
#print axioms
  Pcf.Stacks.dvrRootPuncturedBaseChangeEquivDVRRamificationKummerLocalization
#print axioms Pcf.Stacks.dvrRoot_faithfulSMul_of_faithful_base
#print axioms
  Pcf.Stacks.isUnramifiedAt_of_standardRoot_kummerGenericNormalization_localFactor
#print axioms
  Pcf.Stacks.isUnramifiedAt_of_standardRoot_kummerGenericNormalization_localFactor_of_factorization
#print axioms Pcf.Stacks.etale_of_dvr_kummerUnit_ramification_square
#print axioms Pcf.Stacks.etale_of_dvr_standardRoot_kummerUnit_square
#print axioms Pcf.Stacks.dvrRootPoly_monic
#print axioms Pcf.Stacks.dvrRootAlgebra_finite
#print axioms Pcf.Stacks.dvrRootAlgebra_free
#print axioms Pcf.Stacks.dvrRootAlgebra_finrank
#print axioms Pcf.Stacks.dvrRoot_pow_eq
#print axioms Pcf.Stacks.dvrRootQuotientEquiv
#print axioms Pcf.Stacks.dvrRoot_mem_nonZeroDivisors
#print axioms Pcf.Stacks.dvrRootPoly_isEisensteinAt
#print axioms Pcf.Stacks.dvrRootPoly_irreducible
#print axioms Pcf.Stacks.dvrRootPoly_prime
#print axioms Pcf.Stacks.dvrRootAlgebra_isDomain
#print axioms Pcf.Stacks.dvrRootIdeal_isMaximal
#print axioms Pcf.Stacks.dvrRootAlgebra_isLocalRing
#print axioms Pcf.Stacks.dvrRootAlgebra_isDiscreteValuationRing
#print axioms Pcf.Stacks.dvrRootPoly_map_fractionRing
#print axioms Pcf.Stacks.dvrRootFractionPoly_irreducible
#print axioms Pcf.Stacks.dvrRootFractionAlgebra_isField
#print axioms Pcf.Stacks.dvrRootFractionAlgebra_finrank
#print axioms Pcf.Stacks.dvrRootAlgebra_isIntegralClosure_fractionRing
#print axioms Pcf.Stacks.dvrRootIdeal_ramificationIdx
#print axioms Pcf.Stacks.dvrRootAlgebraToFractionRoot_injective
#print axioms Pcf.Stacks.dvrRootFractionLift_algebraMap
#print axioms Pcf.Stacks.dvrRootFractionLiftAlgHom
#print axioms Pcf.Stacks.dvrRootFractionRing_finrank
#print axioms Pcf.Stacks.dvrRootFractionLiftAlgHom_bijective
#print axioms Pcf.Stacks.dvrRootFractionEquiv
#print axioms Pcf.Stacks.inertiaDeg_eq_one_of_residue_algebraMap_bijective
#print axioms Pcf.Stacks.residue_algebraMap_bijective_of_algEquiv
#print axioms Pcf.Stacks.dvrRootIdeal_under
#print axioms Pcf.Stacks.dvrRootIdeal_liesOver
#print axioms Pcf.Stacks.dvrRootIdeal_inertiaDeg
#print axioms Pcf.Stacks.dvrRootExtension_isTotallyRamifiedAt
#print axioms Pcf.Stacks.dvrRootExtension_clauses_one_to_five
#print axioms Pcf.Stacks.isSeparable_of_finrank_eq_one
#print axioms Pcf.Stacks.dvrRootExtension_isTamelyRamifiedAt
#print axioms Pcf.Stacks.rootOfUnity_eq_one_of_residue_eq_one
#print axioms Pcf.Stacks.restrictRootsOfUnity_residue_injective
#print axioms Pcf.Stacks.rootOfUnity_mem_integralClosure
#print axioms Pcf.Stacks.dvrRootFraction_rootOfUnity_mem_rootAlgebra
#print axioms Pcf.Stacks.dvrRoot_irreducible
#print axioms Pcf.Stacks.dvrRoot_addVal_base
#print axioms Pcf.Stacks.dvrRootAlgebra_rootOfUnity_mem_base
#print axioms Pcf.Stacks.dvrRootFractionRing_rootOfUnity_mem_base
#print axioms Pcf.Stacks.dvrRootFraction_rootOfUnity_mem_base
#print axioms Pcf.Stacks.dvrRootFraction_power_minpoly
#print axioms Pcf.Stacks.dvrRootFraction_power_adjoin_finrank
#print axioms Pcf.Stacks.dvrRootFraction_power_relative_finrank
#print axioms Pcf.Stacks.radical_pow_relative_finrank_mem
#print axioms Pcf.Stacks.dvrRootFractionRing_intermediate_eq_power
#print axioms Pcf.LocalModel.radical_span_algebraMap_eq_span_root
#print axioms Pcf.LocalModel.quotientMap_bijective
#print axioms Pcf.Bounding.mem_minimalPrimes_span_of_mem_minimalPrimes_map
#print axioms Pcf.Bounding.exists_mul_mem_ker_of_mem_minimalPrimes_ker
#print axioms Pcf.Bounding.isLocalization_of_localStructure
#print axioms Pcf.Bounding.formallyEtale_of_localStructure
#print axioms Pcf.Bounding.isLocalizationAway_evalRingHom
#print axioms Pcf.Bounding.exists_isUnit_evalRingHom_single
#print axioms Pcf.Bounding.exists_lift_of_isUnit_single
#print axioms Pcf.BoundingChart.isEtaleAt_of_notMem
#print axioms Pcf.Stacks.IsFiniteDisjointUnionOfStandardTameCovers
#print axioms Pcf.Stacks.HasAbhyankarStandardCoverAt
#print axioms Pcf.BoundingChart.exists_standardPieces
#print axioms Pcf.Stacks.isDomain_of_isRegularLocalRing
#print axioms Pcf.BoundingChart.isEtaleAt_quot_of_pieces
#print axioms Pcf.BoundingChart.isEtaleAt_restriction
#print axioms Pcf.Stacks.etaleLocalOnSource
#print axioms Pcf.Stacks.existsPrimeOverBoth
#print axioms Pcf.Stacks.isReduced_of_etale_of_isDomain
#print axioms Pcf.affineDivisorPointEquiv
#print axioms Pcf.Scheme.Hom.finite_divisorPoint_fiber
#print axioms Pcf.Scheme.Hom.finite_divisorPoint_subtype_fiber
#print axioms Pcf.finite_heightOne_comap_fiber
#print axioms Pcf.height_eq_one_of_liesOver_heightOne
#print axioms Pcf.heightOneUnderOfCodim_surjective
#print axioms Pcf.finite_heightOneUnderOfCodim_fiber
#print axioms Pcf.height_under_eq_of_finite_of_normal
#print axioms Pcf.height_under_eq_of_finite_of_finiteType
#print axioms Pcf.heightOneUnderOfFiniteType_surjective
#print axioms Pcf.finite_heightOneUnderOfFiniteType_fiber
#print axioms Pcf.coheight_apply_eq_one_of_mem_affine_finiteType
#print axioms Pcf.coheight_apply_eq_one_of_finiteType
#print axioms Pcf.SchemeDivisorPoint.mapFiniteDominantFiniteType
#print axioms Pcf.coheight_eq_one_of_finite_preimage
#print axioms Pcf.SchemeDivisorPoint.mapFiniteDominantFiniteType_surjective
#print axioms Pcf.SchemeDivisorPoint.mapFiniteDominantFiniteType_finite_fiber
#print axioms Pcf.finiteDominantFiniteType_divisor_lift
#print axioms Pcf.exists_periodic_point_of_finite_nonempty
#print axioms Pcf.exists_periodic_lift_of_finite_fiber
#print axioms Pcf.exists_periodic_lift_of_surjective_finite_fibers
#print axioms Pcf.NormalizationUnnormDyn.exists_periodic_lift
#print axioms Pcf.exists_periodic_normalization_divisor
#print axioms Pcf.heightOneUnder_surjective
#print axioms Pcf.finite_heightOneUnder_fiber
#print axioms Pcf.affineDivisorUnder_surjective
#print axioms Pcf.isDiscreteValuationRing_localizationAtPrime_of_heightOne
#print axioms Pcf.heightOnePrime_localRing_isDiscreteValuationRing
#print axioms Pcf.isDomain_of_isRegularLocalRing_of_ringKrullDim_eq_one
#print axioms Pcf.isRegularRing_of_isRegularLocalRing_of_ringKrullDim_eq_one
#print axioms Pcf.heightOne_isPrincipal_of_regularLocalRing_dim_two
#print axioms Pcf.isRegularRing_of_isRegularLocalRing_of_isIntegrallyClosed_dim_two
#print axioms Pcf.exists_generator_map_atPrime_regular_dim_two
#print axioms Pcf.mem_minimalPrimes_span_singleton_of_height_eq_one
#print axioms Pcf.exists_principal_localizationAway_of_atPrime_isPrincipal
#print axioms Pcf.exists_principal_map_of_atPrime_isPrincipal
#print axioms Pcf.exists_principal_localizationAway_of_atPrime_regular_dim_two
#print axioms Pcf.exists_principal_localizationAway_of_atPrime_ufd
#print axioms Pcf.exists_principal_localizationAway_of_heightOne
#print axioms Pcf.mem_nonZeroDivisors_of_ringKrullDim_eq_two_of_quotient_eq_one
#print axioms Pcf.isIntegralClosure_localizationAway_of_finite_of_integrallyClosed
#print axioms Pcf.faithfulSMul_localization_algebraMapSubmonoid
#print axioms Pcf.isIntegrallyClosed_localization_algebraMapSubmonoid
#print axioms Pcf.charZero_of_isUnit_natCast
#print axioms Pcf.isUnit_natCast_of_algebraRat
#print axioms Pcf.isUnramifiedAt_of_ramificationIdx_eq_one_of_algebraRat
#print axioms Pcf.isEtaleAt_height_zero_of_charZero_of_integral
#print axioms Pcf.isUnramifiedAt_localization_algebraMapSubmonoid
#print axioms Pcf.LocalBoundingChart.ofFiniteNormalLocalization
#print axioms Pcf.LocalBoundingChart.ofFiniteNormalLocalizationOfDivisorsAt
#print axioms Pcf.LocalBoundingChart.ofFiniteNormalLocalizationOfDivisors
#print axioms Pcf.LocalBoundingChart.ofFiniteNormalLocalizationOfHeightOneDivisorsAt
#print axioms Pcf.LocalBoundingChart.ofFiniteNormalLocalizationOfHeightOneDivisors
#print axioms Pcf.heightOneRam_pos
#print axioms Pcf.heightOneRam_tower
#print axioms Pcf.heightOneBranchIdeal
#print axioms Pcf.ramified_heightOne_lies_over_of_branchIdeal_subset_singleton
#print axioms Pcf.heightOneBranch
#print axioms Pcf.mem_heightOneBranch_iff
#print axioms
  Pcf.heightOneBranchIdeal_subset_singleton_of_heightOneBranch_subset_singleton
#print axioms Pcf.ramified_heightOne_lies_over_of_branch_subset_singleton
#print axioms Pcf.ramified_heightOne_lies_over_of_avoids_other_branch_at
#print axioms Pcf.heightOneDvrExponent_spec
#print axioms Pcf.heightOneRam_eq_dvrExponent
#print axioms Pcf.finite_heightOne_ramified
#print axioms Pcf.divDynOfFiniteNormalSelfAlgebra
#print axioms Pcf.divDynOfFiniteNormalSelfAlgebra_branch
#print axioms Pcf.LocalBoundingChart.toBoundingChart
#print axioms Pcf.LocalBoundingChart.restrictionRingHom
#print axioms Pcf.LocalBoundingChart.restrictionPoint
#print axioms Pcf.LocalBoundingChart.isEtaleAt_restriction
#print axioms Pcf.LocalBoundingChart.formallyEtale_localRingHom
#print axioms Pcf.LocalBoundingChart.affineCrit1_restriction_eq_empty
#print axioms Pcf.ringEquiv_formallyEtale
#print axioms Pcf.formallyEtale_respectsIso
#print axioms Pcf.SchemeStalkBoundingChart.formallyEtale
#print axioms Pcf.SchemeStalkBoundingChart.not_mem_schemeDivisorCrit1
#print axioms Pcf.SchemeStalkBoundingPresentation.toSchemeStalkBoundingChart
#print axioms Pcf.SchemeStalkBoundingPresentation.formallyEtale
#print axioms Pcf.SchemeStalkBoundingPresentation.not_mem_schemeDivisorCrit1
#print axioms Pcf.SchemeStalkBoundingLocalizationPresentation.toSchemeStalkBoundingPresentation
#print axioms Pcf.SchemeStalkBoundingLocalizationPresentation.formallyEtale
#print axioms Pcf.SchemeStalkBoundingLocalizationPresentation.not_mem_schemeDivisorCrit1
#print axioms Pcf.SchemeStalkBoundingChart.toSchemeStalkBoundingLocalizationPresentation
#print axioms Pcf.closedSubschemeStalkBoundingLocalizationPresentation
#print axioms Pcf.closedSubschemeStalkBoundingLocalizationPresentationOfIdeals
#print axioms Pcf.closedSubschemeStalkBoundingLocalizationPresentationOfAmbientMap
#print axioms Pcf.exists_principal_affineBasicOpen_of_atPrime_isPrincipal
#print axioms Pcf.exists_principal_affineBasicOpen_of_atPrime_regular_dim_two
#print axioms Pcf.IdealSheafData.exists_generator_comap_top_of_ideal_eq_span
#print axioms Pcf.exists_principal_comap_affineBasicOpen_of_atPrime_regular_dim_two
#print axioms Pcf.affineIdealSheaf_le_map_of_localBoundingChart
#print axioms Pcf.affineIdealSheafStalkBoundingLocalizationPresentation
#print axioms Pcf.LocalBoundingChart.toSchemeStalkBoundingChart
#print axioms Pcf.LocalBoundingChart.toSchemeStalkBoundingPresentation
#print axioms Pcf.LocalBoundingChart.toSchemeStalkBoundingLocalizationPresentation
#print axioms Pcf.LocalBoundingChart.toGlobalQuotientSchemeStalkBoundingChart
#print axioms
  Pcf.LocalBoundingChart.toGlobalQuotientSchemeStalkBoundingChartOfFiniteNormalLocalizationOfDivisors
#print axioms
  Pcf.LocalBoundingChart.toGlobalQuotientSchemeStalkBoundingLocalizationPresentationOfHeightOneDivisors
#print axioms
  Pcf.LocalBoundingChart.toGlobalQuotientSchemeStalkBoundingLocalizationPresentationOfHeightOneDivisorsAt
#print axioms AlgebraicGeometry.Scheme.Hom.stalkQuotientKerEquiv
#print axioms AlgebraicGeometry.Scheme.Hom.stalkQuotientKerEquiv_mk
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.quotientPoint
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.quotientStalkAlgebra
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.quotientStalk_isLocalization
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.quotientAppLE
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.stalkMap_comp_quotientStalkAlgebraMap
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.comap_quotientPoint_quotientAppLE
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.stalkMapArrowIsoQuotientAppLE
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.subschemeMap_preimage_le
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.quotientAppLE_comp_mk_subschemeMap
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.subschemeMap_ideal_le
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.quotientAppLE_subschemeMap_eq_quotientMap
#print axioms Pcf.finitePreimageModuleFinite
#print axioms Pcf.finitePreimageFaithfulSMul
#print axioms Pcf.pointClosureIdealSheaf_ideal
#print axioms Pcf.pointClosureIdealSheaf_ideal_isPrime
#print axioms Pcf.pointClosureIdealSheaf_ideal_height
#print axioms Pcf.pointClosureIdealSheaf_map
#print axioms Pcf.pointClosureSubschemeMap
#print axioms Pcf.pointClosureSubschemeMap_subschemeι
#print axioms Pcf.pointClosureSubschemeMap_comp
#print axioms Pcf.pointClosureSubschemeMap_id
#print axioms Pcf.end_pow_apply_eq_of_apply_eq
#print axioms Pcf.pointClosureSubschemeMap_iterate_subschemeι
#print axioms Pcf.pointClosureSubschemeMap_iterate
#print axioms Pcf.isFinite_end_pow
#print axioms Pcf.isDominant_end_pow
#print axioms Pcf.affinePrimeOfSchemeDivisorPoint
#print axioms Pcf.exists_pointClosureSubschemePoint
#print axioms Pcf.pointClosureSubschemePoint_subschemeι
#print axioms Pcf.image_mem_pointClosure
#print axioms Pcf.pointClosureSubschemeMap_point
#print axioms Pcf.pointClosureSubschemeMap_isFinite
#print axioms Pcf.pointClosureSubschemeι_mem
#print axioms Pcf.SchemeDivisorPoint.mem_affine_of_pointClosurePoint_mem
#print axioms Pcf.pointClosureSubschemeMap_isDominant
#print axioms Pcf.pointClosureSubschemeMap_surjective
#print axioms Pcf.pointClosureSubschemePreimage
#print axioms Pcf.pointClosureSubschemeMap_preimage
#print axioms Pcf.coheight_apply_eq_one_of_mem_affine
#print axioms Pcf.coheight_apply_eq_one
#print axioms Pcf.SchemeDivisorPoint.mapFiniteDominantNormal
#print axioms Pcf.SchemeDivisorPoint.closureMapFiniteDominantNormal
#print axioms Pcf.SchemeDivisorPoint.closurePreimageFiniteDominantNormal
#print axioms Pcf.SchemeDivisorPoint.closureMap_preimageFiniteDominantNormal
#print axioms Pcf.SchemeDivisorPoint.closurePreimage_mem_finitePreimage
#print axioms Pcf.map_ambientPrimeOfQuotientPoint
#print axioms Pcf.ambientPrimeOfQuotientPoint_eq_primeIdealOf
#print axioms Pcf.ambientPrimeLocalizationRingEquivStalk
#print axioms Pcf.divisorQuotientLocalizationRingEquivStalkOfEq
#print axioms Pcf.divisorQuotientLocalizationRingEquivStalk
#print axioms Pcf.isRegularLocalRing_divisorQuotientLocalization
#print axioms Pcf.ringKrullDim_divisorQuotientLocalization
#print axioms Pcf.ambientPrimeOfQuotientPoint_comap
#print axioms Pcf.ringKrullDim_eq_two_of_cartier_quotient_eq_one
#print axioms Pcf.isRegularLocalRing_stalk_of_not_mem_stalkSingularLocus
#print axioms Pcf.SchemeDivisorPoint.image_mem_affine_of_closurePoint_mem
#print axioms Pcf.avoids_other_heightOneBranch_of_not_mem_finiteAffineOtherBranchLocus
#print axioms Pcf.SchemeDivisorPoint.closurePreimage_under_eq_primeIdealOf
#print axioms Pcf.SchemeDivisorPoint.closurePoint_under_eq_primeIdealOf
#print axioms Pcf.pointClosurePoint_under_eq_primeIdealOf
#print axioms Pcf.SchemeDivisorPoint.imageDivisorCartierDataAtOfUFD
#print axioms Pcf.SchemeDivisorPoint.imageDivisorCartierDataAtOfRegularDimTwo
#print axioms
  Pcf.closedSubschemeStalkBoundingLocalizationPresentationOfFiniteNormalAt
#print axioms
  Pcf.closedSubschemeStalkBoundingLocalizationPresentationOfFiniteDominantNormalAt
#print axioms
  Pcf.closedSubschemeStalkBoundingLocalizationPresentationOfFiniteDominantNormal
#print axioms
  Pcf.closedSubschemeStalkBoundingLocalizationPresentationOfFiniteDominantNormalOfCartier
#print axioms
  Pcf.pointClosureStalkBoundingLocalizationPresentationOfFiniteDominantNormal
#print axioms
  Pcf.SchemeDivisorPoint.closureStalkBoundingLocalizationPresentationOfFiniteDominantNormal
#print axioms
  Pcf.SchemeDivisorPoint.closureStalkBoundingLocalizationPresentationOfFiniteDominantNormalOfCartier
#print axioms
  Pcf.SchemeDivisorPoint.closureStalkBoundingLocalizationPresentationOfFiniteDominantNormalOfStep0At
#print axioms Pcf.SchemeDivisorPoint.closureStalkBoundingLocalizationOfStep0UFDAt
#print axioms
  Pcf.SchemeDivisorPoint.closureStalkBoundingLocalizationOfStep0RegularDimTwoAt
#print axioms Pcf.SchemeDivisorPoint.invariantClosureMap_iterate
#print axioms Pcf.SchemeDivisorPoint.invariantClosureMap_isFinite
#print axioms
  Pcf.SchemeDivisorPoint.invariantClosureMap_locallyOfFinitePresentation
#print axioms
  Pcf.SchemeDivisorPoint.invariantClosureStalkBoundingLocalizationOfStep0At
#print axioms
  Pcf.SchemeDivisorPoint.closureStalkBoundingLocalizationPresentationOfFiniteDominantNormalOfStep0
#print axioms Pcf.LocalBoundingChart.schemeDivisorCrit1_restriction_eq_empty
#print axioms Pcf.schemeDivisorCrit0_subset_crit1
#print axioms Pcf.formallyEtale_stalkMap_iff
#print axioms Pcf.isOpen_formallyEtale_stalkLocus
#print axioms Pcf.map_genericPoint_eq_of_isDominant
#print axioms Pcf.formallyEtale_stalkMap_genericPoint_of_exists
#print axioms Pcf.formallyEtale_stalkMap_genericPoint_of_finite_dominant_charZero
#print axioms Pcf.exists_formallyEtale_stalk_iterate_of_exists
#print axioms Pcf.isClosed_schemeCrit1Locus
#print axioms Pcf.finite_schemeDivisorPoint_mem_of_isClosed
#print axioms Pcf.schemeDivisorCrit1_finite_of_isClosed
#print axioms Pcf.schemeDivisorCrit1_finite_of_isClosed_of_exists_formallyEtale
#print axioms Pcf.schemeDivisorCrit1_finite_of_exists_formallyEtale
#print axioms Pcf.isReduced_vanishingIdeal_subscheme
#print axioms Pcf.isIntegral_vanishingIdeal_subscheme
#print axioms Pcf.pointClosureSubscheme_isIntegral
#print axioms Pcf.pointClosureSubschemeι_genericPoint
#print axioms Pcf.isRegularLocalRing_stalk_genericPoint
#print axioms Pcf.genericPoint_not_mem_stalkSingularLocus
#print axioms Pcf.stalkSingularLocus_ne_univ
#print axioms Pcf.stalkSingularLocus_pointClosureSubscheme_ne_univ
#print axioms Pcf.SchemeDivisorPoint.isRegularLocalRing_stalk
#print axioms Pcf.SchemeDivisorPoint.not_mem_stalkSingularLocus
#print axioms Pcf.schemeDivisorPoint_stalkSingularLocus_eq_empty
#print axioms Pcf.finite_schemeDivisorPoint_stalkSingularLocus
#print axioms Pcf.genericPoint_not_mem_ambient_stalkSingularLocus
#print axioms Pcf.stalkSingularLoci_pointClosureSubscheme_ne_univ
#print axioms Pcf.RingHom.Etale.localRingHom_formallyEtale
#print axioms Pcf.AlgebraicGeometry.Etale.stalkMap_formallyEtale
#print axioms Pcf.LocalBoundingChart.restrictionRingHom_etale
#print axioms Pcf.LocalBoundingChart.restrictionScheme_etale
#print axioms Pcf.schemeResLETopIso
#print axioms Pcf.affineResLEArrowIso
#print axioms Pcf.affineQuotientArrowIso
#print axioms Pcf.SchemeAffineLocalBoundingPresentation.toSchemeLocalBoundingPresentation
#print axioms Pcf.LocalBoundingChart.toSchemeLocalBoundingPresentation
#print axioms Pcf.LocalBoundingChart.toSchemeAffineLocalBoundingPresentation
#print axioms Pcf.SchemeLocalBoundingPresentation.restrictedEtale
#print axioms Pcf.SchemeLocalBoundingPresentation.formallyEtale
#print axioms Pcf.SchemeLocalBoundingPresentation.not_mem_schemeDivisorCrit1
#print axioms Pcf.SchemeAffineLocalBoundingPresentation.formallyEtale
#print axioms Pcf.SchemeAffineLocalBoundingPresentation.not_mem_schemeDivisorCrit1
#print axioms Pcf.schemeDivisorMap_val
#print axioms Pcf.schemeDivisorMap_finite_fiber
#print axioms Pcf.schemeDivisorMap_comm_of_comm
#print axioms Pcf.schemeDivisorMap_iterate_val
#print axioms Pcf.schemeDivisorCrit0_tower
#print axioms Pcf.schemeDivisorCrit1_tower
#print axioms Pcf.SchemeNormalizationUnnormDyn.crit0_subset_crit1
#print axioms Pcf.SchemeNormalizationUnnormDyn.crit0_tower
#print axioms Pcf.SchemeNormalizationUnnormDyn.crit1_tower
#print axioms Pcf.SchemeNormalizationUnnormDyn.finite_iterate
#print axioms Pcf.SchemeNormalizationUnnormDyn.finitePresentation_iterate
#print axioms Pcf.SchemeNormalizationUnnormDyn.toNormalizationUnnormDyn
#print axioms Pcf.ramificationIdx_pos_of_quasiFinite
#print axioms Pcf.SchemeDivisorPoint.stalk_isDiscreteValuationRing
#print axioms Pcf.stalkMap_injective_of_dominant_integral
#print axioms Pcf.schemeDivisorRam_comp
#print axioms Pcf.schemeDivisorRam_id
#print axioms Pcf.schemeDivisorRam_pos
#print axioms Pcf.schemeDivisorRam_eq_one_of_formallyEtale
#print axioms Pcf.schemeDivisorRam_gt_one_mem_crit1
#print axioms Pcf.coheight_apply_eq_of_finite_dominant_normal
#print axioms Pcf.SchemeDivisorPoint.mapFiniteDominantNormal_surjective
#print axioms Pcf.SchemeDivisorPoint.mapFiniteDominantNormal_finite_fiber
#print axioms Pcf.divDynOfFiniteDominantNormal
#print axioms Pcf.divDynOfFiniteDominantNormalOfExistsFormallyEtale
#print axioms Pcf.divDynOfFiniteDominantNormalNoetherian
#print axioms Pcf.divDynOfFiniteDominantNormalCharZero
#print axioms Pcf.divDynOfFiniteDominantNormal_iterate_step_val
#print axioms Pcf.divDynOfFiniteDominantNormal_iterRam
#print axioms Pcf.DivDyn.ext_of_step_ram
#print axioms Pcf.divDynOfFiniteDominantNormal_pow_eq_iter
#print axioms Pcf.divDynOfFiniteDominantNormalCharZero_pow_eq_iter
#print axioms Pcf.divDynOfFiniteNormalization
#print axioms Pcf.divDynOfFiniteNormalization_iterRam
#print axioms Pcf.schemeNormalizationUnnormDynOfFiniteType
#print axioms Pcf.InvariantDivisorSchemeNormalizationPcfSetup.ofActualAmbient
#print axioms Pcf.isDedekindDomain_of_formallyUnramified_local
#print axioms Pcf.formallyUnramified_normalization_of_local
#print axioms Pcf.ramificationIdx_normalization_eq_one_of_local
#print axioms Pcf.ramificationIdx_normalization_eq_one_of_baseChange
#print axioms Pcf.not_formallyUnramified_of_one_lt_ramificationIdx_normalization
#print axioms Pcf.ramificationIdx_normalization_eq_one_of_localized_baseChange
#print axioms
  Pcf.not_formallyUnramified_of_one_lt_ramificationIdx_localized_normalization
#print axioms Pcf.bijective_algebraMap_of_local_birational
#print axioms Pcf.ramificationIdx_eq_one_of_localized_birational_baseChange
#print axioms
  Pcf.not_formallyUnramified_of_one_lt_ramificationIdx_localized_birational
#print axioms Pcf.ramificationIdx_eq_one_of_local_birational_square
#print axioms Pcf.schemeStalkBirationalAt_of_isIso_generic_stalkMap
#print axioms Pcf.not_formallyUnramified_stalkMap_of_one_lt_schemeDivisorRam
#print axioms Pcf.normalization_square_pow
#print axioms Pcf.schemeDivisorRam_gt_one_mem_crit0_of_finite_birational
#print axioms Pcf.schemeNormalizationUnnormDynOfFiniteBirational
#print axioms Pcf.schemeGlobalNormalization_isIntegral
#print axioms Pcf.schemeGlobalNormalizationMap_isIntegralHom
#print axioms Pcf.schemeGlobalNormalizationMap_isDominant
#print axioms Pcf.schemeGlobalNormalizationMap_isIso_generic_stalkMap
#print axioms Pcf.schemeGlobalNormalizationMap_stalkBirationalAt
#print axioms Pcf.schemeGlobalNormalizationMap_surjective
#print axioms Pcf.schemeGenericEndomorphism_comp
#print axioms Pcf.schemeNormalizationComparison_comp
#print axioms Pcf.schemeNormalizationGenericMap_comp
#print axioms Pcf.schemeGlobalNormalizationLift_comp
#print axioms Pcf.schemeGlobalNormalizationLift_isIntegralHom
#print axioms Pcf.schemeGlobalNormalizationLift_isDominant
#print axioms Pcf.schemeGlobalNormalizationLift_isFinite
#print axioms Pcf.schemeGenericToNormalization_comparison
#print axioms Pcf.schemeNormalizationComparisonInv
#print axioms Pcf.schemeGenericToNormalization_comparisonInv
#print axioms Pcf.schemeNormalizationComparisonInv_comp_comparison_map
#print axioms Pcf.schemeNormalizationComparisonInv_comp_comparison
#print axioms Pcf.schemeNormalizationComparison_comp_comparisonInv
#print axioms Pcf.schemeNormalizationComparisonIso
#print axioms Pcf.schemeNormalizationComparison_isIso
#print axioms Pcf.schemeGenericInclusion_preimage_eq_top
#print axioms Pcf.schemeGenericInclusion_sectionsIso
#print axioms Pcf.schemeGlobalNormalization_preimage_integrallyClosed
#print axioms Pcf.schemeGlobalNormalization_stalk_integrallyClosed
#print axioms Pcf.isNormalScheme_of_stalk_integrallyClosed
#print axioms Pcf.schemeGlobalNormalization_isNormal
#print axioms Pcf.finite_integralClosure_of_finiteType
#print axioms Pcf.finite_schemeGenericIntegralClosure
#print axioms Pcf.schemeGlobalNormalizationMap_isFinite_of_affineFiniteType
#print axioms Pcf.schemeGlobalNormalizationMap_isFinite
#print axioms Pcf.schemeGlobalNormalizationUnnormDyn
#print axioms Pcf.schemeGlobalNormalizationUnnormDynOfFiniteType
#print axioms Pcf.SchemeNormalizationPcfSetupChart.key1
#print axioms Pcf.SchemeNormalizationPcfSetupChart.res_pcf1
#print axioms Pcf.SchemeNormalizationPcfSetupChart.norm_pcf
#print axioms
  Pcf.InvariantDivisorSchemeNormalizationPcfSetup.toSchemeNormalizationPcfSetupChart
#print axioms Pcf.InvariantDivisorSchemeNormalizationPcfSetup.key1
#print axioms Pcf.InvariantDivisorSchemeNormalizationPcfSetup.res_pcf1
#print axioms Pcf.InvariantDivisorSchemeNormalizationPcfSetup.norm_pcf
#print axioms Pcf.InvariantDivisorSchemeNormalizationPcfSetup.norm_pcf_of_iter
#print axioms Pcf.BoundingChart.affineCrit1_restriction_eq_empty
#print axioms Pcf.BoundingChart.not_mem_affineCrit1_restriction
#print axioms Pcf.PcfSetupChart.key1
#print axioms Pcf.PcfSetupChart.toPcfSetup1
#print axioms Pcf.PcfSetupChart.res_pcf1
#print axioms Pcf.PcfSetupChart.res_pcf
#print axioms Pcf.PcfSetupChart.res_pcf1_of_iter

/-! ## §`sec:examples`: Examples `ex:squaring` and `ex:squaring-P2`, and the non-vacuity witness -/

#print axioms Pcf.Examples.squaringP1_branch
#print axioms Pcf.Examples.squaringP1_pcf
#print axioms Pcf.Examples.squaringP1_branch_iter
#print axioms Pcf.Examples.diagonalSquaring_bound
#print axioms Pcf.Examples.diagonalSquaring_res_pcf

/-! ## §`sec:bounding`: Examples `ex:cusp` and `ex:branch-singular` -/

#print axioms Pcf.Examples.Cusp.cuspParam
#print axioms Pcf.Examples.Cusp.jacobian_cuspSource
#print axioms Pcf.Examples.Cusp.mem_cuspAlg_iff
#print axioms Pcf.Examples.Cusp.X_not_mem_cuspAlg
#print axioms Pcf.Examples.Cusp.isFractionRing_cuspAlg
#print axioms Pcf.Examples.Cusp.isIntegralClosure_cuspAlg
#print axioms Pcf.Examples.Cusp.integralClosure_cuspAlg_eq_top
#print axioms Pcf.Examples.Cusp.cusp_inter_branch
#print axioms Pcf.Examples.Cusp.coneParam
#print axioms Pcf.Examples.Cusp.coneMap_restrict

/-! ## The join is inhabited with genuine ramification -/

#print axioms Pcf.Examples.isPrime_iff_singleton
#print axioms Pcf.Examples.noetherianSpace_cofNat
#print axioms Pcf.Examples.cofiniteGeometry
#print axioms Pcf.Examples.resDyn_branch
#print axioms Pcf.Examples.resDyn_pcf

/-! ## `branch_finite'` fully discharged on `Spec S`

`Pcf.divDynOfSpectrum` builds a `Pcf.DivDyn` assuming only lying over and generic
étaleness: `ram`, `ram_pos` and the ramified-implies-non-étale compatibility are all
theorems, and no `Pcf.PurityData` — hence no Zariski–Nagata input — is needed. -/

#print axioms Pcf.mem_nonEtaleLocus_of_one_lt_ramificationIdx
#print axioms Pcf.ramificationIdx_eq_one_of_notMem_nonEtaleLocus
#print axioms Pcf.specRam
#print axioms Pcf.specRam_pos
#print axioms Pcf.subset_nonEtaleLocus_of_one_lt_specRam
#print axioms Pcf.finite_ramified
#print axioms Pcf.comap_surjective_of_isIntegral_of_injective
#print axioms Pcf.specStep_surjective
#print axioms Pcf.divDynOfSpectrum

/-! ## The purity layer wired into Theorem `thm:normal-invariant`

`branch_finite'` for the restricted system is no longer a field on this route. -/

#print axioms Pcf.resDivDynOfPurity
#print axioms Pcf.resDivDynOfAlgebra
#print axioms Pcf.PcfGeometry.ofPurityData
#print axioms Pcf.PcfGeometry.res_pcf_of_purityData
#print axioms Pcf.exists_nonEtale_of_branch_finite
#print axioms Pcf.Examples.resDynOfPurity
#print axioms Pcf.Examples.resDynOfPurity_branch
#print axioms Pcf.Examples.resDynOfPurity_pcf

/-! ## Zariski–Nagata purity

Two fields of `Pcf.PurityData` are discharged for an actual algebra, and the assumed
local form is restated so that it matches Stacks Tag 0BMB rather than exceeding it.
Purity itself is still assumed; see `lean/AXIOMS.md`, entry P1. -/

#print axioms Pcf.isClosed_nonEtaleLocus
#print axioms Pcf.closure_eq_univ_of_specCodim_eq_zero
#print axioms Pcf.nonEtaleLocus_eq_empty_iff
#print axioms Pcf.purityDataOfAlgebra
#print axioms Pcf.purityDataOfEtale
#print axioms Pcf.codim_eq_one_of_algebra
#print axioms Pcf.finite_isPrime_subset_nonEtaleLocus
#print axioms Pcf.ZariskiNagata.etale_of_codim_one_etale
#print axioms Pcf.PurityData.ofZariskiNagata
#print axioms Pcf.ZariskiNagata.codim_eq_one
#print axioms Pcf.PurityData.toZariskiNagata
#print axioms Pcf.PurityData.ofZariskiNagata_toZariskiNagata
#print axioms Pcf.localPurity_of_codim_le_one
#print axioms Pcf.PurityData.ofCodimLeOne

/-! ## Stacks Tag 0EYF, clauses 1–2, and the retracted witness interfaces

The Kummer-algebra material is correct standalone mathematics. The witness interfaces
`Pcf.KummerWitness`/`Pcf.UnramifiedWitness` are retained only as the record of a retracted
assumption; no field is valued in them. -/

#print axioms Abhyankar.isStandardEtale_adjoinRoot_of_separable
#print axioms Abhyankar.isStandardEtale
#print axioms Abhyankar.etale
#print axioms Abhyankar.ramificationIdx_eq_one
#print axioms Abhyankar.nontrivial_adjoinRoot
#print axioms Abhyankar.exists_isPrime
#print axioms Abhyankar.subst
#print axioms Abhyankar.substEquiv
#print axioms Abhyankar.etale_ramifiedPoly
#print axioms Pcf.KummerWitness.eq_one
#print axioms Pcf.KummerWitness.ofKummer
#print axioms Pcf.KummerWitness.ofTame
#print axioms Pcf.KummerWitness.cubic
#print axioms Pcf.nonempty_kummerWitness_iff
#print axioms Pcf.kummerWitness_iff_unramifiedWitness
#print axioms Pcf.KummerWitness.ofEqOne
#print axioms Abhyankar.finrank
#print axioms Abhyankar.etale_ramifiedPoly_general
#print axioms Abhyankar.not_etale_wild
#print axioms Abhyankar.not_etale_of_not_isUnit

/-! ## §`sec:charp`: Example `ex:wild`, the wild counterexample -/

#print axioms Pcf.Examples.CharP.orbit_natDegree
#print axioms Pcf.Examples.CharP.orbit_infinite

/-! ## Appendix `app:other-defs`: the unnormalized loci, and Theorem `thm:normal-invariant`
in its `1`-PCF form

`Pcf.UnnormDyn` carries Proposition `prop:loci-compare` and Lemma `lem:tower-unnormalized`
as *fields* (assumed, see `lean/AXIOMS.md` §B.8); `Pcf.PcfSetup1.key1` is the étale form of
Theorem `thm:bounding`, also assumed. Everything printed here is proved from those. -/

#print axioms Pcf.UnnormDyn.branch_iter_subset_branch0
#print axioms Pcf.UnnormDyn.branch_subset_branch0
#print axioms Pcf.UnnormDyn.branch0_subset_branch1
#print axioms Pcf.UnnormDyn.branch1_finite
#print axioms Pcf.UnnormDyn.pcSet_subset_pcSet0
#print axioms Pcf.UnnormDyn.pcSet0_subset_pcSet1
#print axioms Pcf.UnnormDyn.pcf0_of_pcf1
#print axioms Pcf.UnnormDyn.pcf_of_pcf0
#print axioms Pcf.UnnormDyn.orbit_unnormalized_zero
#print axioms Pcf.UnnormDyn.orbit_unnormalized_one
#print axioms Pcf.UnnormDyn.orbit_unnormalized_one'
#print axioms Pcf.UnnormDyn.pcSet1_subset_of_branch1_subset
#print axioms Pcf.UnnormDyn.pcf1_of_branch1_subset
#print axioms Pcf.PcfSetup1.toPcfSetup
#print axioms Pcf.PcfSetup1.branch1_iter_subset_bound
#print axioms Pcf.PcfSetup1.res_pcf1
#print axioms Pcf.PcfSetup1.res_pcf0
#print axioms Pcf.PcfSetup1.res_pcf
#print axioms Pcf.PcfSetup1.res_pcf1_of_iter

/-! ## Normalized and unnormalized divisor carriers

`Pcf.NormalizationUnnormDyn` keeps divisors on the normalization separate from divisors on
the possibly nonnormal scheme.  The PCF transfer below uses finite normalization fibers rather
than a definitional identification of the two carriers. -/

#print axioms Pcf.NormalizationUnnormDyn.normalization_iterate
#print axioms Pcf.NormalizationUnnormDyn.normalization_image_branch_iter_subset_branch0
#print axioms Pcf.NormalizationUnnormDyn.normalization_image_pcSet_subset_pcSet0
#print axioms Pcf.NormalizationUnnormDyn.pcSet_subset_normalization_preimage_pcSet0
#print axioms Pcf.NormalizationUnnormDyn.norm_pcf_of_pcf0
#print axioms Pcf.NormalizationUnnormDyn.norm_pcf_of_pcf1
#print axioms Pcf.NormalizationUnnormDyn.pcSet1_subset_of_branch1_subset
#print axioms Pcf.NormalizationUnnormDyn.pcf1_of_branch1_subset
#print axioms Pcf.NormalizationPcfSetup.branch1_iter_subset_bound
#print axioms Pcf.NormalizationPcfSetup.res_pcf1
#print axioms Pcf.NormalizationPcfSetup.norm_pcf
#print axioms Pcf.NormalizationPcfSetup.norm_pcf_of_iter
#print axioms Pcf.NormalizationPcfSetupChart.key1
#print axioms Pcf.NormalizationPcfSetupChart.toNormalizationPcfSetup
#print axioms Pcf.NormalizationPcfSetupChart.norm_pcf
#print axioms Pcf.NormalizationPcfSetupChart.norm_pcf_of_iter

/-! ## Canonical normalization and ramified-cover descent

The normalized postcritical set is defined downstairs from actual divisor orbits, then
identified with the image of the upstairs postcritical set.  Cover descent derives its
branch identity from actual stalk ramification in the commuting square. -/

#print axioms Pcf.NormalizationUnnormDyn.branch_eq_normalization_image
#print axioms Pcf.NormalizationUnnormDyn.pcSet_eq_normalization_image
#print axioms Pcf.NormalizationUnnormDyn.pcf_iff_norm_pcf
#print axioms Pcf.SchemeNormalizationUnnormDyn.pcf_iff_norm_pcf
#print axioms Pcf.schemeNormalizedBranch_eq_normalization_image
#print axioms Pcf.schemeNormalizedBranch_eq_normalization_image_reducedFiberBranch
#print axioms Pcf.mem_schemeNormalizedBranch_iff_nonreduced_normalizedFiber
#print axioms Pcf.schemeNormalizedPcSet_eq_normalization_image
#print axioms Pcf.schemeNormalizedPCF_iff_normalization
#print axioms Pcf.DivDyn.pcSet_subset_ramifiedCoverBound
#print axioms Pcf.DivDyn.pcf_of_ramified_branch_union
#print axioms Pcf.DivDyn.RamifiedCover.branch_union
#print axioms Pcf.DivDyn.RamifiedCover.pcf
#print axioms Pcf.schemeRamifiedCover
#print axioms Pcf.scheme_pcf_of_ramified_cover
#print axioms Pcf.formallyEtale_stalkMap_genericPoint_of_cover_charZero
#print axioms Pcf.schemeDivisorCrit1_finite_of_cover_charZero
#print axioms Pcf.schemeRamifiedCoverCharZero
#print axioms Pcf.scheme_pcf_of_ramified_cover_charZero
#print axioms Pcf.schemeGenericMorphism_comp
#print axioms Pcf.schemeGenericMorphism_comp_morphism
#print axioms Pcf.schemeGlobalNormalizationMorphism
#print axioms Pcf.schemeGlobalNormalizationMorphism_comp
#print axioms Pcf.schemeGenericToNormalization_morphism
#print axioms Pcf.schemeGlobalNormalizationMorphism_unique
#print axioms Pcf.schemeGlobalNormalizationMorphism_comp_morphism
#print axioms Pcf.schemeGlobalNormalizationMorphism_comm
#print axioms Pcf.schemeGlobalNormalizationMorphism_isFinite_of_finiteType
#print axioms Pcf.schemeGlobalNormalizationMorphism_locallyOfFinitePresentation
#print axioms Pcf.schemeGlobalNormalizationMorphism_isDominant
#print axioms Pcf.schemeGlobalNormalization_noetherianSpace
#print axioms Pcf.schemeGlobalNormalization_generic_charZero
#print axioms Pcf.schemeGlobalNormalizationDivisorMap_surjective
#print axioms Pcf.schemeGlobalNormalizationDivisorMap_finite_fiber
#print axioms Pcf.schemeGlobalNormalizationRamifiedCover
#print axioms Pcf.schemeGlobalNormalizationRamifiedCover_map_val
#print axioms Pcf.schemeGlobalNormalizationRamifiedCover_ram
#print axioms Pcf.schemeNormalizedPCF_of_ramified_cover
#print axioms Pcf.schemeGenericMorphism_id
#print axioms Pcf.schemeGlobalNormalizationMorphism_id
#print axioms Pcf.schemeGlobalNormalizationLift_id
#print axioms Pcf.schemeGlobalNormalizationLift_comp_lift
#print axioms Pcf.schemeGlobalNormalizationMorphism_pow
#print axioms Pcf.schemeGlobalNormalizationLift_pow
#print axioms Pcf.schemeGlobalNormalizationUnnormDyn_norm_eq
#print axioms Pcf.schemeGlobalNormalizationUnnormDyn_norm_pow
#print axioms Pcf.schemeNormalizedPcSet_pow
#print axioms Pcf.schemeNormalizedPCF_pow_iff

/-! ## Actual invariant-divisor geometry

The codimension-two flag theorem is proved for schemes locally of finite type over a
field.  The remaining declarations construct the genuine exceptional sets, affine
divisor transport, and canonical normalization dynamics attached to an invariant
divisor. -/

#print axioms Pcf.isRegularLocalRing_iff_of_ringEquiv
#print axioms Pcf.isRegularLocalRing_localizationAtPrime_iff
#print axioms Pcf.isRegularRing_of_isLocalization
#print axioms Pcf.finiteType_exists_regular_presentation
#print axioms Pcf.primeRegularLocus
#print axioms Pcf.preimage_primeRegularLocus_of_isLocalization
#print axioms Pcf.isOpen_primeRegularLocus_iff
#print axioms Pcf.primeRegularLocus_eq_univ
#print axioms Pcf.isOpen_primeRegularLocus_of_isRegularRing
#print axioms Pcf.isRegularLocalRing_stalk_Spec_iff
#print axioms Pcf.stalkSingularLocus_Spec_eq
#print axioms Pcf.isClosed_stalkSingularLocus_Spec_iff
#print axioms Pcf.isRegularLocalRing_stalk_openImmersion_iff
#print axioms Pcf.preimage_stalkSingularLocus_openImmersion
#print axioms Pcf.preimage_stalkSingularLocus_fromSpec
#print axioms Pcf.isClosed_stalkSingularLocus_iff_affine
#print axioms Pcf.isOpen_primeRegularLocus_of_isArtinianRing
#print axioms Pcf.isClosed_stalkSingularLocus_Spec_of_moduleFinite
#print axioms Pcf.stalkSingularLocus_Spec_eq_empty
#print axioms Pcf.stalkSingularLocus_affineSpace_eq_empty
#print axioms Pcf.isRegularLocalRing_of_flat_of_formallyUnramified
#print axioms Pcf.isRegularRing_of_etale
#print axioms Pcf.isRegularLocalRing_of_isSmoothAt
#print axioms Pcf.isRegularRing_of_smooth
#print axioms Pcf.isRegularLocalRing_stalk_of_mem_smoothLocus
#print axioms Pcf.stalkSingularLocus_subset_compl_smoothLocus
#print axioms Pcf.exists_retraction_kerCotangentToTensor_of_formallySmooth
#print axioms Pcf.exists_retraction_residueField_kerCotangentToTensor_of_perfectField
#print axioms Pcf.injective_residueField_kerCotangentToTensor_of_perfectField
#print axioms Pcf.finrank_residueField_tensor_kaehlerDifferential_of_perfectField
#print axioms Pcf.finrank_residueField_tensor_kaehlerDifferential_atPrime_of_charZero
#print axioms Pcf.formallySmooth_iff_conormal_finrank_bound_of_perfectField
#print axioms Pcf.spanFinrank_maximalIdeal_le_two_of_principal_kernel
#print axioms Pcf.spanFinrank_maximalIdeal_le_add_one_of_principal_kernel
#print axioms Pcf.isRegularLocalRing_of_quotient_nonZeroDivisor
#print axioms Pcf.isRegularLocalRing_of_principal_kernel_of_dim_one
#print axioms Pcf.isRegularLocalRing_of_principal_quotient_of_dim_one
#print axioms Pcf.two_le_height_of_height_one_lt
#print axioms Pcf.height_eq_two_of_divisorFlag_finiteType
#print axioms Pcf.Scheme.IdealSheafData.quotientPoint_height
#print axioms Pcf.SchemeDivisorPoint.closureDivisor_coheight_of_mem_affine_finiteType
#print axioms Pcf.SchemeDivisorPoint.closureDivisor_coheight_of_finiteType
#print axioms Pcf.pointClosureSubscheme_irreducible
#print axioms Pcf.pointClosureSubscheme_reduced
#print axioms Pcf.pointClosureSubscheme_integral
#print axioms Pcf.pointClosureSubscheme_locallyNoetherian
#print axioms Pcf.pointClosureSubscheme_noetherian
#print axioms Pcf.pointClosureSubscheme_genericPoint
#print axioms Pcf.SchemeDivisorPoint.not_mem_closure_of_ne
#print axioms Pcf.SchemeDivisorPoint.two_le_coheight_closureDivisor
#print axioms Pcf.schemeDivisorPointOfAffinePrime
#print axioms Pcf.schemeDivisorPointOfAffinePrime_injective
#print axioms Pcf.schemeDivisorPointOfAffinePrime_affinePrime
#print axioms Pcf.schemeDivisorPointOfAffinePrime_mem_closure
#print axioms Pcf.schemeDivisorPointOfAffinePrime_map
#print axioms Pcf.invariantDivisorMeets
#print axioms Pcf.invariantDivisorMeets_finite
#print axioms Pcf.invariantDivisorSing
#print axioms Pcf.invariantDivisorSing_regular
#print axioms Pcf.invariantDivisorSing_finite_of_isClosed
#print axioms Pcf.schemeStalkAlgebraOfField
#print axioms Pcf.schemeStalkCharZeroOfField
#print axioms Pcf.schemeAffineRationalAlgebraOfField
#print axioms Pcf.SchemeDivisorPoint.invariantClosureMap_dominant
#print axioms Pcf.invariantDivisorNormalization
#print axioms Pcf.invariantDivisorNormalization_g
#print axioms Pcf.invariantDivisorNormalization_iterate_step_val
#print axioms Pcf.SchemeDivisorPoint.invariantClosureIterate_source_mem
#print axioms Pcf.ramificationIdx_eq_of_localization_square
#print axioms Pcf.schemeDivisorRam_eq_heightOneRam
#print axioms Pcf.localDivisorFiber_isReduced_iff_ramificationIdx_eq_one
#print axioms Pcf.divisorFiber_isReduced_iff_forall_ramificationIdx_eq_one
#print axioms Pcf.schemeFiberRestrictIso
#print axioms Pcf.schemeFiberIsoOfArrowIso
#print axioms Pcf.schemeDivisorFiber_isReduced_iff_forall_schemeDivisorRam_eq_one
#print axioms Pcf.schemeReducedFiberBranch
#print axioms Pcf.mem_schemeReducedFiberBranch_iff
#print axioms Pcf.schemeReducedFiberBranch_eq_divDyn_branch
#print axioms Pcf.schemeDivisorPointOfAffinePrime_mem_branch
#print axioms Pcf.not_mem_finiteAffineOtherBranchLocus_of_meets
#print axioms Pcf.invariantDivisorStep0LocalDataOfRegular
#print axioms Pcf.invariantDivisorSetupOfFiniteRegularityCorrection
#print axioms Pcf.invariantDivisorSetupOfClosedSingularLoci
#print axioms
  Pcf.invariantDivisorNormalization_norm_pcf_of_finiteRegularityCorrection
#print axioms Pcf.invariantDivisorNormalization_norm_pcf_of_closedSingularLoci
#print axioms Pcf.exists_principalOpen_map_eq_span_of_isPrincipal_atPrime
#print axioms Pcf.finite_schemeDivisorPoint_stalkSingularLocus_of_perfectField
#print axioms Pcf.mem_basicOpen_iff_notMem_primeIdealOf
#print axioms Pcf.exists_open_invariantDivisor_regularityCorrection
#print axioms Pcf.invariantDivisorSing_finite_of_perfectField
#print axioms Pcf.invariantDivisorSetupOfFiniteType
#print axioms Pcf.invariantDivisorNormalization_norm_pcf_of_finiteType

/-! ## Scheme-level PCF all the way down -/

#print axioms Pcf.SchemeNormalizedPCFOfFiniteType
#print axioms Pcf.schemeNormalizedPCFOfFiniteType_iff_lift
#print axioms Pcf.schemeNormalizedPCFOfFiniteType_pow_iff
#print axioms Pcf.schemeNormalizedPCFOfFiniteType_of_cover
#print axioms Pcf.pointClosureSubschemeMap_comm
#print axioms Pcf.schemeEnd_pow_comm
#print axioms Pcf.InvariantDivisorCoveringInputs
#print axioms Pcf.schemeAffineAlgebraOfField
#print axioms Pcf.schemeAffineAlgebraOfField_finiteType
#print axioms Pcf.schemeNormalizedPCFOfFiniteType_iff
#print axioms Pcf.invariantDivisor_schemeNormalizedPCFOfFiniteType
#print axioms Pcf.periodicDivisor_schemeNormalizedPCFOfFiniteType
#print axioms Pcf.schemeDivisorIterateOfFiniteType
#print axioms Pcf.schemeDivisorIterateOfFiniteType_val
#print axioms Pcf.schemeDivisorIterateOfFiniteType_periodic
#print axioms Pcf.pcfAllTheWayDown_scheme
#print axioms Pcf.SchemePCFAllTheWayDownAtDepth
#print axioms Pcf.SchemePcfCoveringAtDepth
#print axioms Pcf.schemePCFAllTheWayDownAtDepth_of_cover
#print axioms Pcf.schemePCFAllTheWayDown_of_cover
#print axioms Pcf.scheme_orderKrullDim_eq_topologicalKrullDim
#print axioms Pcf.SchemeDivisorFlag
#print axioms Pcf.SchemeDivisorPoint.lt_genericPoint
#print axioms Pcf.SchemeDivisorFlag.toLTSeriesData
#print axioms Pcf.SchemeDivisorFlag.length_le_topologicalKrullDim
#print axioms Pcf.SchemeDivisorFlag.length_le_of_topologicalKrullDim_le
#print axioms Pcf.SchemeDivisorFlag.isEmpty_succ_of_topologicalKrullDim_le
#print axioms Pcf.SchemePcfDescentStep
#print axioms Pcf.SchemePcfDescentBranch
#print axioms Pcf.SchemePcfDescentBranch.toDivisorFlag
#print axioms Pcf.SchemePcfDescentBranch.length_le_of_topologicalKrullDim_le
#print axioms Pcf.SchemePcfDescentBranch.isEmpty_succ_of_topologicalKrullDim_le
#print axioms Pcf.schemePCFAllTheWayDownAtDepth_of_succ
#print axioms Pcf.schemePCFAllTheWayDownAtDepth_mono
#print axioms Pcf.schemePCFAllTheWayDownAtDepth_succ_of_isEmpty_branch
#print axioms
  Pcf.SchemePcfDescentBranch.isEmpty_succ_of_topologicalKrullDim_le_of_le
#print axioms Pcf.schemePCFAllTheWayDown_of_cover_to_dimension
#print axioms Pcf.PcfAllTheWayDownLocalTheorems
#print axioms Pcf.SchemePCFAllTheWayDown
#print axioms Pcf.schemePcfCoveringAtDepthOfLocalTheorems
#print axioms Pcf.pcfAllTheWayDown_charZero

/-! ## Purity and Abhyankar run (2026-10-16)

Every non-internal theorem of the modules added in the purity/Abhyankar run
(`ai/2026-10-16-purity-abhyankar-completion/`), and of the formerly orphaned purity and
Abhyankar modules now imported by `Pcf`.  The headline theorems are first. -/

#print axioms Pcf.Stacks.zariskiNagataPurity
#print axioms Pcf.Stacks.stacksEtaleAt_of_zariskiNagataPurity
#print axioms Pcf.Stacks.exists_etale_of_zariskiNagataPurity
#print axioms Pcf.Stacks.palomar_zariskiNagataPurity
#print axioms Pcf.Stacks.abhyankarLemma
#print axioms Pcf.Stacks.palomar_abhyankarLemma
#print axioms Pcf.Stacks.abhyankarLemma_tame
#print axioms Pcf.Stacks.SchemeLevel.tag0EYG
#print axioms Pcf.Stacks.SchemeLevel.tag0EYH
#print axioms Pcf.pcfAllTheWayDownLocalTheorems
#print axioms Pcf.pcfAllTheWayDown_charZero_unconditional
#print axioms Pcf.Palomar.pcfAllTheWayDown_charZero
#print axioms Pcf.Palomar.pcfAllTheWayDown_charZero_unconditional

-- Pcf.Stacks.Abhyankar.DVRAbhyankarDivisible
#print axioms Pcf.Stacks.exists_unit_pow_eq_of_pow_mul_eq
#print axioms Pcf.Stacks.formallyUnramified_dvrRoot_of_dvd
#print axioms Pcf.Stacks.maximalIdeal_eq_span_root_of_dvd
#print axioms Pcf.Stacks.surjective_of_isLocalHom_of_dvr

-- Pcf.Stacks.Abhyankar.StrictComponentClassification
#print axioms Pcf.Stacks.AlgHom.extendScalarsOfIsFractionRing_apply
#print axioms Pcf.Stacks.charZero_of_forall_nat_isUnit
#print axioms Pcf.Stacks.rootPoly_fractionRing_irreducible

-- Pcf.Stacks.Abhyankar.StrictGenericPresentation
#print axioms Pcf.Stacks.exists_mul_eq_strictRootCoverToRootFractionField
#print axioms Pcf.Stacks.strictRootCoverToRootFractionField_root

-- Pcf.Stacks.Abhyankar.StrictHeightOneTransport
#print axioms
  Pcf.Stacks.PointedEtaleNeighborhood.exists_rootExponent_fractionRing_equiv_of_strictRootComponentData
#print axioms Pcf.Stacks.StrictRootComponentData.etaleAway
#print axioms Pcf.Stacks.StrictRootComponentData.faithfulSMul
#print axioms Pcf.Stacks.StrictRootComponentData.finite
#print axioms Pcf.Stacks.StrictRootComponentData.isDomain
#print axioms Pcf.Stacks.StrictRootComponentData.isIntegrallyClosed
#print axioms Pcf.Stacks.StrictRootComponentData.mk.sizeOf_spec
#print axioms Pcf.Stacks.StrictRootComponentData.towerComponent
#print axioms Pcf.Stacks.StrictRootComponentData.towerRoot
#print axioms Pcf.Stacks.StrictRootComponentData.unramified
#print axioms Pcf.Stacks.forall_height_one_isUnramifiedAt_of_root_mem
#print axioms Pcf.Stacks.isUnramifiedAt_of_isEtaleAt
#print axioms Pcf.Stacks.mem_minimalPrimes_span_of_height_eq_one
#print axioms Pcf.Stacks.under_eq_of_height_eq_one_of_mem

-- Pcf.Stacks.Abhyankar.StrictHeightOneUnramified
#print axioms Pcf.Stacks.StrictRootComponentPreData.exists_aeval_eq
#print axioms Pcf.Stacks.StrictRootComponentPreData.exists_aeval_mul_eq_aeval_of_generic
#print axioms Pcf.Stacks.StrictRootComponentPreData.faithfulSMul_component
#print axioms Pcf.Stacks.exists_aeval_eq_of_mem_adjoin

-- Pcf.Stacks.Abhyankar.StrictHenselizationCompletionFlat
#print axioms Pcf.Stacks.Module.Flat.of_forall_exists_flat_algebra
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.isUnit_toLocalColimitAlgHom_of_point_ne_zero
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimit_completion_flat
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimit_completion_flat_stageLocal
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimit_completion_isNoetherianRing
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimit_flat_stage
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimit_isNoetherianRing
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimit_isRegularLocalRing
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.map_maximalIdeal_stageLocal
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.ringKrullDim_localColimit_eq
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.stageLocalToLocalColimit_algebraMap
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.stagePrime_isPrime
#print axioms
  Pcf.Stacks.PointedEtaleNeighborhood.toLocalColimitAlgHom_mem_maximalIdeal_of_point_eq_zero
#print axioms Pcf.Stacks.adicCompletion_flat_of_flat_of_map_maximalIdeal
#print axioms Pcf.Stacks.exists_basis_quotient_maximalIdeal_powers_of_flat
#print axioms Pcf.Stacks.exists_linearCombination_reduceModIdeal_bijective_of_flat
#print axioms Pcf.Stacks.maximalAdicCompletion_flat_of_flat_of_map_maximalIdeal
#print axioms Pcf.Stacks.quotientPowSMulTopEquivMap_mk
#print axioms Pcf.Stacks.quotientPowSMulTopEquivMap_symm_mk
#print axioms Pcf.Stacks.quotientPowSMulTopEquivMap_symm_transitionMap
#print axioms Pcf.Stacks.quotientPowSMulTopEquivMap_transitionMap
#print axioms Pcf.Stacks.quotientSMulTopEquivQuotientMap_mk
#print axioms Pcf.Stacks.smul_top_eq_restrictScalars_map_pow_smul_top

-- Pcf.Stacks.Abhyankar.StrictHenselizationLocalize
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.aeval_smul_derivative_scaleRoots
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.algebraMap_ne_zero_of_mem
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.atPrimeAlgebra_isScalarTower
#print axioms
  Pcf.Stacks.PointedEtaleNeighborhood.colimitBaseChangeRingHom_bijective_of_isLocalization
#print axioms
  Pcf.Stacks.PointedEtaleNeighborhood.colimitBaseChangeRingHom_injective_of_isLocalization
#print axioms
  Pcf.Stacks.PointedEtaleNeighborhood.colimitBaseChangeRingHom_surjective_of_isLocalization
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.colimitLocalizationRingEquiv_apply
#print axioms
  Pcf.Stacks.PointedEtaleNeighborhood.exists_localizationBaseChange_equalizing_refinement
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.exists_localizationBaseChange_refinement
#print axioms
  Pcf.Stacks.PointedEtaleNeighborhood.exists_localizationBaseChange_refinement_of_toColimit_eq
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.exists_mem_mul_eq_one_tmul
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.exists_mem_mul_eq_zero_of_one_tmul_eq_zero
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.isUnit_algebraMap_colimit_of_mem
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.isUnit_of_mul_isUnit_right_of_commRing
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimitAtPrimeRingEquiv_algebraMap
#print axioms
  Pcf.Stacks.PointedEtaleNeighborhood.localColimitBaseChangeRingHom_bijective_of_isLocalization
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimitLocalizationRingEquiv_algebraMap
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimitLocalizationRingEquiv_apply
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localPoint_comp_localColimitLocalizationRingEquiv
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localizationBaseChange_final
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.scaleRoots_comp_C_mul_X

-- Pcf.Stacks.Abhyankar.StrictNormalDecomposition
#print axioms Pcf.Stacks.IsIdempotentElem.isIntegral
#print axioms Pcf.Stacks.IsIdempotentElem.mul_aeval_mul
#print axioms Pcf.Stacks.IsStacksNormalRing.exists_completeOrthogonalIdempotents
#print axioms Pcf.Stacks.IsStacksNormalRing.isCoprime_of_mem_minimalPrimes
#print axioms Pcf.Stacks.IsStacksNormalRing.of_isLocalization
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.etale_localizationAway_baseChange
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimit_isStacksNormalRing_of_regular_divisor
#print axioms
  Pcf.Stacks.PointedEtaleNeighborhood.localColimit_tensor_exists_normalDomain_decomposition
#print axioms
  Pcf.Stacks.PointedEtaleNeighborhood.localColimit_tensor_localizationAway_isStacksNormalRing
#print axioms Pcf.Stacks.exists_completeOrthogonalIdempotents_of_isIntegralClosure_localizationAway

-- Pcf.Stacks.Abhyankar.StrictNormalizationColimit
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.algebraMap_mem_nonZeroDivisors_localColimit
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.exists_refinement_forall_eq_zero
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.exists_refinement_map_eq_zero_of_map_eq_zero
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.ker_algebraMap_eq_maximalIdeal
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimitIntegralClosureEquiv.congr_simp
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimitIntegralClosureEquiv_val
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimit_isIntegralClosure
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimit_isIntegralClosure_localizationAway
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.localColimit_toIntegralClosure_bijective
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.quotient_localColimit_isRegularLocalRing
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.quotient_span_localColimit_isRegularLocalRing
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.quotient_span_localColimit_isRegularRing
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.toIntegralClosure_map_val

-- Pcf.Stacks.Abhyankar.StrictRootComponent
#print axioms
  Pcf.Stacks.PointedEtaleNeighborhood.exists_strictRootComponentPreData_strictBaseChangeFactor
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.strictBaseChangeFactor_faithfulSMul
#print axioms Pcf.Stacks.StrictRootComponentPreData.etaleAway
#print axioms Pcf.Stacks.StrictRootComponentPreData.faithfulSMul
#print axioms Pcf.Stacks.StrictRootComponentPreData.finite
#print axioms Pcf.Stacks.StrictRootComponentPreData.generic
#print axioms Pcf.Stacks.StrictRootComponentPreData.isDomain
#print axioms Pcf.Stacks.StrictRootComponentPreData.isIntegrallyClosed
#print axioms Pcf.Stacks.StrictRootComponentPreData.mk.sizeOf_spec
#print axioms Pcf.Stacks.StrictRootComponentPreData.toData_carrier
#print axioms Pcf.Stacks.StrictRootComponentPreData.towerComponent
#print axioms Pcf.Stacks.StrictRootComponentPreData.towerRoot
#print axioms Pcf.Stacks.etale_localizationAway_quotient_idempotent
#print axioms Pcf.Stacks.exists_strictRootComponentPreData
#print axioms Pcf.Stacks.faithfulSMul_quotient_idempotent
#print axioms Pcf.Stacks.injective_includeRight_fractionRing
#print axioms Pcf.Stacks.integralClosure_faithfulSMul
#print axioms Pcf.Stacks.integralClosure_finite_of_etale_of_isDomain
#print axioms Pcf.Stacks.integralClosure_isIntegrallyClosed
#print axioms Pcf.Stacks.integralClosure_isLocalization_away
#print axioms Pcf.Stacks.isEtaleAt_of_isLocalization_away
#print axioms Pcf.Stacks.isEtaleAt_quotient_idempotent
#print axioms Pcf.Stacks.nonempty_strictRootComponentPreData_of_factor
#print axioms Pcf.Stacks.strictRootCover_tensor_away_nontrivial

-- Pcf.Stacks.Abhyankar.StrictRootCover
#print axioms Pcf.Stacks.IsIdempotentElem.eq_zero_or_eq_one_of_isDomain
#print axioms Pcf.Stacks.IsSepClosed.of_ringEquiv
#print axioms Pcf.Stacks.bijective_algebraMap_of_finite_etale_local_of_isSepClosed
#print axioms Pcf.Stacks.divisorLocalization_irreducible
#print axioms Pcf.Stacks.divisorLocalization_isDiscreteValuationRing
#print axioms Pcf.Stacks.divisorLocalization_isRegularLocalRing
#print axioms Pcf.Stacks.divisorPrime_height_eq_one
#print axioms Pcf.Stacks.divisorPrime_isPrime
#print axioms Pcf.Stacks.faithfulSMul_of_flat_of_isDomain
#print axioms Pcf.Stacks.isDiscreteValuationRing_localization_atPrime_of_height_eq_one
#print axioms Pcf.Stacks.isLocalRing_of_isDomain_of_finite_of_henselian
#print axioms Pcf.Stacks.isLocalRing_of_quotient_of_le_jacobson
#print axioms Pcf.Stacks.map_maximalIdeal_le_jacobson_of_isIntegral
#print axioms Pcf.Stacks.map_maximalIdeal_le_of_isMaximal_of_isIntegral
#print axioms Pcf.Stacks.span_singleton_isPrime_of_quotient_isDomain
#print axioms Pcf.Stacks.strictRootCover_degree_pos
#print axioms Pcf.Stacks.strictRootCover_faithfulSMul
#print axioms Pcf.Stacks.strictRootCover_finite
#print axioms Pcf.Stacks.strictRootCover_isDomain
#print axioms Pcf.Stacks.strictRootCover_isIntegral
#print axioms Pcf.Stacks.strictRootCover_isIntegrallyClosed
#print axioms Pcf.Stacks.strictRootCover_isLocalHom
#print axioms Pcf.Stacks.strictRootCover_isLocalRing
#print axioms Pcf.Stacks.strictRootCover_isNoetherianRing
#print axioms Pcf.Stacks.strictRootCover_isRegularLocalRing
#print axioms Pcf.Stacks.strictRootCover_localization_span_root_isDiscreteValuationRing
#print axioms Pcf.Stacks.strictRootCover_quotient_isRegularLocalRing
#print axioms Pcf.Stacks.strictRootCover_quotient_isRegularRing
#print axioms Pcf.Stacks.strictRootCover_residueField_bijective
#print axioms Pcf.Stacks.strictRootCover_residueField_isSepClosed
#print axioms Pcf.Stacks.strictRootCover_span_root_height_eq_one
#print axioms Pcf.Stacks.strictRootCover_span_root_isPrime
#print axioms Pcf.Stacks.strictRootCover_span_root_under
#print axioms Pcf.Stacks.strictRoot_mem_jacobson
#print axioms Pcf.Stacks.strictRoot_mem_maximalIdeal
#print axioms Pcf.Stacks.strictRoot_mem_nonZeroDivisors
#print axioms Pcf.Stacks.strictRoot_mem_of_isMaximal
#print axioms Pcf.Stacks.strictRoot_pow

-- Pcf.Stacks.Abhyankar.Tag0EYG
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.ker_geometricPointAtAlgebra
#print axioms Pcf.Stacks.hasAbhyankarStandardCoverAt_of_mem_divisor
#print axioms Pcf.Stacks.henselianLocalRing_of_ringEquiv

-- Pcf.Stacks.Common.EtaleNormal
#print axioms Pcf.Stacks.IsStacksNormalRing.of_etale
#print axioms Pcf.Stacks.eq_of_comap_le_of_etale
#print axioms Pcf.Stacks.height_eq_height_under_of_etale
#print axioms Pcf.Stacks.height_eq_height_under_of_flat_of_quasiFiniteAt
#print axioms Pcf.Stacks.isArtinianRing_isReduced_tensor_fractionRing_of_etale
#print axioms Pcf.Stacks.isDomain_isIntegrallyClosed_atPrime_of_etale
#print axioms Pcf.Stacks.isDomain_isIntegrallyClosed_atPrime_of_etale_of_isDomain
#print axioms Pcf.Stacks.isField_localization_tensor_fractionRing_of_etale
#print axioms Pcf.Stacks.isIntegrallyClosedIn_of_isLocalization
#print axioms Pcf.Stacks.isIntegrallyClosedIn_tensor_fractionRing_of_smooth
#print axioms Pcf.Stacks.isIntegrallyClosed_of_etale
#print axioms Pcf.Stacks.isStacksNormalRing_of_etale_of_isDomain

-- Pcf.Stacks.Common.RegularLocalization
#print axioms Pcf.Stacks.IsRegularLocalRing.of_isLocalization_atPrime
#print axioms Pcf.Stacks.RegularLocalization.instIsRegularLocalRingLocalizationAtPrime
#print axioms Pcf.Stacks.RegularLocalization.instIsRegularRingOfIsRegularLocalRing
#print axioms Pcf.Stacks.isRegularLocalRing_iff_globalDimension_lt_top
#print axioms Pcf.Stacks.isRegularLocalRing_localization_atPrime
#print axioms Pcf.Stacks.isRegularRing_of_isRegularLocalRing

-- Pcf.Stacks.Common.RegularNormal
#print axioms Pcf.Stacks.exists_regular_pair_of_two_le_ringKrullDim
#print axioms Pcf.Stacks.isIntegrallyClosed_of_isRegularLocalRing
#print axioms Pcf.Stacks.isIntegrallyClosed_of_isRegularRing
#print axioms Pcf.Stacks.isRegularRing_localization_atPrime
#print axioms Pcf.Stacks.isStacksNormalRing_of_isRegularLocalRing
#print axioms Pcf.Stacks.isStacksNormalRing_of_isRegularRing
#print axioms Pcf.Stacks.mem_span_singleton_of_maximalIdeal_mul_le
#print axioms Pcf.Stacks.mem_span_singleton_of_regular_pair

-- Pcf.Stacks.Purity.Completion
#print axioms Pcf.Stacks.IsAdicComplete.of_le
#print axioms Pcf.Stacks.exists_sum_smul_of_mem_span_smul
#print axioms Pcf.Stacks.faithfullyFlat_adicCompletion
#print axioms Pcf.Stacks.isAdicComplete_map_of_finite
#print axioms Pcf.Stacks.isAdicComplete_map_self_of_finite
#print axioms Pcf.Stacks.isAdicComplete_map_span_singleton_of_finite
#print axioms Pcf.Stacks.isAdicComplete_maximalIdeal_quotient
#print axioms Pcf.Stacks.isAdicComplete_of_finite
#print axioms Pcf.Stacks.isAdicComplete_quotient
#print axioms Pcf.Stacks.isAdicComplete_span_singleton_of_finite
#print axioms Pcf.Stacks.isNoetherianRing_adicCompletion
#print axioms Pcf.Stacks.isRegularLocalRing_adicCompletion
#print axioms Pcf.Stacks.map_maximalIdeal_adicCompletion
#print axioms Pcf.Stacks.mem_smul_top_of_sub_mem_smul_of_smodEq
#print axioms Pcf.Stacks.ringKrullDim_adicCompletion

-- Pcf.Stacks.Purity.CompletionDescent
#print axioms Pcf.Stacks.finiteNormalPuncturedEtalePurity_of_completion_puncturedSpectrumPurity
#print axioms Pcf.Stacks.finiteNormalPuncturedEtalePurity_of_faithfullyFlat_puncturedSpectrumPurity
#print axioms Pcf.Stacks.preimage_puncturedSpectrum_eq_of_map_maximalIdeal_eq
#print axioms Pcf.Stacks.puncturedEtale_tensorProduct_of_map_maximalIdeal_eq

-- Pcf.Stacks.Purity.RegularPairSections
#print axioms Pcf.Stacks.openSections_bijective_of_regularPair_of_puncturedEtale
#print axioms Pcf.Stacks.pullbackSections_bijective_of_regularPair_of_puncturedEtale

-- Pcf.Stacks.Purity.FormalEtaleLift
#print axioms Pcf.Stacks.Ideal.Quotient.mk_smul_base
#print axioms Pcf.Stacks.algHom_lift_unique_of_formallyUnramified
#print axioms Pcf.Stacks.algebraMap_localization_away_injective
#print axioms Pcf.Stacks.algebraMap_mem_nonZeroDivisors_of_isSMulRegular
#print axioms Pcf.Stacks.awayToAwayLeftₐ_algebraMap
#print axioms Pcf.Stacks.awayToAwayRightₐ_algebraMap
#print axioms Pcf.Stacks.away_algHom_ext
#print axioms Pcf.Stacks.away_mapₐ_algebraMap
#print axioms Pcf.Stacks.exists_algHom_lift_of_isAdicComplete
#print axioms Pcf.Stacks.exists_algHom_lift_of_regular_pair
#print axioms Pcf.Stacks.exists_algHom_of_compatible_of_isAdicComplete
#print axioms Pcf.Stacks.exists_algHom_of_regular_pair_of_agree
#print axioms Pcf.Stacks.forall_of_isSMulRegular_quotient
#print axioms Pcf.Stacks.isNilpotent_ker_away_mapₐ
#print axioms Pcf.Stacks.isNilpotent_ker_factorₐ_span_pow
#print axioms Pcf.Stacks.isSMulRegular_quotSMulTop_quotient_of_forall
#print axioms Pcf.Stacks.isSMulRegular_quotient_of_forall
#print axioms Pcf.Stacks.ker_away_mapₐ_le
#print axioms Pcf.Stacks.mem_smul_top_iff_exists
#print axioms Pcf.Stacks.mem_span_pow_smul_top_iff
#print axioms Pcf.Stacks.span_pow_succ_le
#print axioms Pcf.Stacks.span_pow_succ_le_of_le
#print axioms Pcf.Stacks.span_pow_succ_succ_le

-- Pcf.Stacks.Purity.HenselianFiniteEtaleLift
#print axioms Pcf.Stacks.BoolFamily.etale
#print axioms Pcf.Stacks.HasFiniteEtaleLift.of_adjoinRoot
#print axioms Pcf.Stacks.HasFiniteEtaleLift.of_algEquiv
#print axioms Pcf.Stacks.HasFiniteEtaleLift.prod
#print axioms Pcf.Stacks.etale_adjoinRoot_of_isCoprime_derivative
#print axioms Pcf.Stacks.etale_prod
#print axioms Pcf.Stacks.etale_quotient_map
#print axioms Pcf.Stacks.exists_adjoinRoot_algEquiv_of_closedFibre_field
#print axioms Pcf.Stacks.exists_finite_etale_lift_of_henselianLocalRing
#print axioms Pcf.Stacks.exists_isIdempotentElem_sub_mem_of_isIntegral_of_henselian
#print axioms Pcf.Stacks.exists_monic_factorization_lift_of_henselian
#print axioms Pcf.Stacks.hasFiniteEtaleLift_of_finrank_eq
#print axioms Pcf.Stacks.isCoprime_of_isCoprime_map_of_le_jacobson
#print axioms Pcf.Stacks.restrictFiniteEtaleToHypersurface_essSurj
#print axioms Pcf.Stacks.subsingleton_of_subsingleton_closedFibre
#print axioms Polynomial.MonicDegreeEq.mk.congr_simp

-- Pcf.Stacks.Purity.HypersurfaceLiftingComplete
#print axioms Pcf.Stacks.etale_localization_away_of_isEtaleAt
#print axioms Pcf.Stacks.etale_of_hypersurface_lift
#print axioms Pcf.Stacks.exists_algHom_bijective_of_hypersurface_lift
#print axioms Pcf.Stacks.exists_algHom_of_pullback_iso
#print axioms Pcf.Stacks.exists_isRegular_triple
#print axioms Pcf.Stacks.henselianLocalRing_of_isAdicComplete
#print axioms Pcf.Stacks.hypersurfaceFiniteEtaleLifting_of_isAdicComplete
#print axioms Pcf.Stacks.isSMulRegular_quotSMulTop_congr
#print axioms Pcf.Stacks.isSMulRegular_quotSMulTop_quotient_span_pow_of_isWeaklyRegular
#print axioms Pcf.Stacks.isSMulRegular_quotSMulTop_self_iff
#print axioms Pcf.Stacks.isSMulRegular_quotient_span_pow_of_isWeaklyRegular
#print axioms Pcf.Stacks.isWeaklyRegular_pair_of_triple
#print axioms Pcf.Stacks.localized_bijective_of_mod_isSMulRegular
#print axioms Pcf.Stacks.mem_smul_top_iff_mem_span
#print axioms Pcf.Stacks.mem_span_of_scaleRoots_aeval_eq_zero_of_isStacksNormalRing
#print axioms Pcf.Stacks.puncturedSpectrumScheme.congr_simp
#print axioms Pcf.Stacks.regularLocal_puncturedSpectrumPurity_induction_step_of_isAdicComplete

-- Pcf.Stacks.Purity.PuncturedEtaleOfPointwise
#print axioms Pcf.Stacks.etale_opens_ι_comp_of_forall_isEtaleAt
#print axioms Pcf.Stacks.etale_puncturedSpectrum_pullback_of_forall_isEtaleAt
#print axioms Pcf.Stacks.etale_respectsIso

-- Pcf.Stacks.Purity.Tag0BMA
#print axioms Pcf.Stacks.finiteNormalPuncturedEtalePurity_of_isRegularLocalRing
#print axioms Pcf.Stacks.puncturedSpectrumPurity_of_finiteNormalPuncturedEtalePurity
#print axioms Pcf.Stacks.puncturedSpectrumPurity_of_isRegularLocalRing
#print axioms Pcf.Stacks.puncturedSpectrumPurity_of_isRegularLocalRing_dimension_two
#print axioms Pcf.Stacks.puncturedSpectrumPurity_of_isRegularLocalRing_of_isAdicComplete

-- Pcf.Stacks.Purity.Tag0BMB
#print axioms Pcf.Stacks.palomar_zariskiNagataPurity_of_inputs
#print axioms Pcf.Stacks.zariskiNagataPurity_of_inputs

-- Pcf.Stacks.Purity.Tag0BMBLocalModel
#print axioms Pcf.Stacks.faithfullyFlat_localization_atPrime
#print axioms Pcf.Stacks.flat_of_faithfullyFlat_of_flat
#print axioms Pcf.Stacks.formallyEtale_localization_atPrime
#print axioms Pcf.Stacks.formallyUnramified_of_faithfullyFlat_of_formallyEtale
#print axioms Pcf.Stacks.hasZariskiNagataPurityAt_of_lowerHeight
#print axioms Pcf.Stacks.height_eq_height_under_of_finite_of_isIntegrallyClosed
#print axioms Pcf.Stacks.height_eq_height_under_of_mem_minimalPrimes
#print axioms Pcf.Stacks.height_le_height_under_of_mem_minimalPrimes
#print axioms Pcf.Stacks.height_map_fiber_eq_zero_of_mem_minimalPrimes
#print axioms Pcf.Stacks.injective_algebraMap_of_finite_of_ringKrullDim_le
#print axioms Pcf.Stacks.isDomain_isIntegrallyClosed_localization_of_etale
#print axioms Pcf.Stacks.isEtaleAt_of_flat_of_formallyUnramified
#print axioms Pcf.Stacks.isEtaleAt_of_le
#print axioms Pcf.Stacks.mem_minimalPrimes_of_quasiFiniteAt
#print axioms Pcf.Stacks.module_finite_localization_atPrime_of_unique

-- Pcf.Stacks.Purity.Tag0BMBScheme
#print axioms Pcf.Stacks.IsStacksNormalRing.isDomain_isIntegrallyClosed_of_isLocalRing
#print axioms Pcf.Stacks.formallyUnramified_stalkMap_iff
#print axioms Pcf.Stacks.formallyUnramified_stalkMap_of_stacksUnramifiedAt
#print axioms Pcf.Stacks.isRegularLocalRing_atPrime_of_eq
#print axioms Pcf.Stacks.stacksEtaleAt_of_isEtaleAt
#print axioms Pcf.Stacks.stacksEtaleAt_of_zariskiNagataPurity

-- Pcf.Stacks.Purity.Tag0BMBSchemeAPI
#print axioms Pcf.Stacks.HasRingHomProperty.resLE_iff_appLE
#print axioms Pcf.Stacks.HasRingHomProperty.resLE_of_comp_ι
#print axioms Pcf.Stacks.HasRingHomProperty.comp_ι_iff_resLE
#print axioms Pcf.Stacks.HasRingHomProperty.appLE_of_comp_ι
#print axioms Pcf.Stacks.HasRingHomProperty.exists_appLE_iff_exists_comp_ι
#print axioms Pcf.Stacks.HasRingHomProperty.appLE_of_appLE_of_le
#print axioms Pcf.Stacks.IsZariskiLocalAtSource.iff_forall_exists_comp_ι
#print axioms Pcf.Stacks.IsZariskiLocalAtSource.isOpen_setOf_exists_comp_ι
#print axioms Pcf.Stacks.IsZariskiLocalAtSource.exists_comp_ι_comp_iff
#print axioms Pcf.Stacks.mem_basicOpen_of_notMem_primeIdealOf
#print axioms Pcf.Stacks.appLE_basicOpen_of_away
#print axioms Pcf.Stacks.stacksEtaleAt_iff_exists_etale
#print axioms Pcf.Stacks.StacksEtaleAt.etale_appLE
#print axioms Pcf.Stacks.etale_appLE_of_le
#print axioms Pcf.Stacks.forall_stacksEtaleAt_iff
#print axioms Pcf.Stacks.stacksEtaleAt_of_etale
#print axioms Pcf.Stacks.isOpen_setOf_stacksEtaleAt
#print axioms Pcf.Stacks.stacksEtaleAt_comp_iff_of_isOpenImmersion
#print axioms Pcf.Stacks.stacksEtaleAt_ι_comp_iff
#print axioms Pcf.Stacks.stacksUnramifiedAt_iff_exists
#print axioms Pcf.Stacks.forall_stacksUnramifiedAt_iff
#print axioms Pcf.Stacks.isOpen_setOf_stacksUnramifiedAt
#print axioms Pcf.Stacks.stacksUnramifiedAt_comp_iff_of_isOpenImmersion
#print axioms Pcf.Stacks.stacksUnramifiedAt_iff_stalkMap
#print axioms Pcf.Stacks.StacksEtaleAt.stacksUnramifiedAt
#print axioms Pcf.Stacks.quasiFiniteAt_iff_appLE
#print axioms Pcf.Stacks.stacksQuasiFiniteAt_iff
#print axioms Pcf.Stacks.stacksQuasiFiniteAt_iff_quasiFiniteAt
#print axioms Pcf.Stacks.forall_stacksQuasiFiniteAt_iff
#print axioms Pcf.Stacks.StacksUnramifiedAt.stacksQuasiFiniteAt
#print axioms Pcf.Stacks.StacksEtaleAt.stacksQuasiFiniteAt
#print axioms Pcf.Stacks.isOpen_setOf_stacksQuasiFiniteAt
#print axioms Pcf.Stacks.stacksQuasiFiniteAt_comp_iff_of_isOpenImmersion
#print axioms Pcf.Stacks.exists_etale_of_zariskiNagataPurity
#print axioms Pcf.Stacks.exists_etale_of_zariskiNagataPurity_of_locallyOfFiniteType

-- Pcf.Stacks.Purity.GabberPolynomialIdempotent
#print axioms Pcf.Stacks.exists_isIdempotentElem_sub_mem_of_aeval_eq_zero_of_gabberPolynomial

-- Pcf.Stacks.Abhyankar.DivisorNormalizationTransport
#print axioms Pcf.Stacks.isUnramifiedAt_localizedNormalization_of_dvrRootPuncturedGenericEquiv
#print axioms Pcf.Stacks.isUnramifiedAt_of_localizedNormalizationAtPrime
#print axioms Pcf.Stacks.localizedDVRRootNormalizationRingHom_comp_algebraMap
#print axioms Pcf.Stacks.localizedNormalizationEquivDVRRootPuncturedNormalization_algebraMap

-- Pcf.Stacks.Abhyankar.LocalizedNormalizationComparison
#print axioms Pcf.Stacks.isIntegralClosure_of_modelEquiv
#print axioms Pcf.Stacks.localizationBaseChangeIntegralClosureEquiv.congr_simp
#print axioms Pcf.Stacks.localizationBaseChangeIntegralClosureEquiv_val
#print axioms Pcf.Stacks.localizationBaseChange_isIntegralClosure
#print axioms Pcf.Stacks.localizedNormalizationAlgebra_algebraMap
#print axioms Pcf.Stacks.localizedNormalizationEquivIntegralClosure_algebraMap
#print axioms Pcf.Stacks.localizedNormalization_isIntegralClosure
#print axioms Pcf.Stacks.localizedNormalization_isScalarTower

-- Pcf.Stacks.Purity.DiscriminantGlobal
#print axioms Pcf.Stacks.Algebra.etale_of_isUnit_discr_of_basis_global
#print axioms Pcf.Stacks.Algebra.formallyEtale_of_discr_ne_zero_of_basis_global
#print axioms Pcf.Stacks.Algebra.isUnramifiedAt_of_formallyEtale_fiber
#print axioms Pcf.Stacks.Algebra.traceForm_pi_nondegenerate_factors
#print axioms Pcf.Stacks.Algebra.traceForm_prod_nondegenerate_factors

-- Pcf.Stacks.Purity.StandardEtaleSectionLifting
#print axioms Pcf.Stacks.exists_algHom_lift_of_isStandardEtale

-- Pcf.Stacks.Purity.DimensionTwo
#print axioms Pcf.Stacks.Algebra.isEtaleAt_of_puncturedSpectrum_pullback_etale
#print axioms Pcf.Stacks.exists_prime_height_one_of_isRegularLocalRing_dimension_two
#print axioms
  Pcf.Stacks.finiteNormalPuncturedEtalePurity_of_isRegularLocalRing_of_isIntegrallyClosed_dimension_two

-- Pcf.Stacks.Purity.LocalEtaleSectionLifting
#print axioms Pcf.Stacks.exists_algHom_lift_of_etale_of_isLocalRing

-- Pcf.Stacks.Purity.IntegralIdempotentPolynomial
#print axioms Pcf.Stacks.exists_monic_aeval_eq_zero_map_eq_X_pow_mul_X_sub_one_pow

/-! ## Example `ex:pinched`: the pinched plane

Ring-level facts are proved outright. The dynamical statements take `o ∈ crit₀(g)` as a
hypothesis (`pcSet0_infinite`) or stipulate it (`nodeUnnormDyn`); the fibre-length
computation behind it is not formalized. -/

#print axioms Pcf.Examples.Pinched.sqMap_mem
#print axioms Pcf.Examples.Pinched.sqMap_mem_of_mem
#print axioms Pcf.Examples.Pinched.w_mem
#print axioms Pcf.Examples.Pinched.z_sq_mem
#print axioms Pcf.Examples.Pinched.z_mul_w_sub_one_mem
#print axioms Pcf.Examples.Pinched.z_cubed_sub_mem
#print axioms Pcf.Examples.Pinched.exists_reduce
#print axioms Pcf.Examples.Pinched.glueIdeal_le_adjoin
#print axioms Pcf.Examples.Pinched.sub_C_mem_glueIdeal
#print axioms Pcf.Examples.Pinched.adjoin_gens_eq
#print axioms Pcf.Examples.Pinched.comp_sq_mem
#print axioms Pcf.Examples.Pinched.sqOrbit_eq
#print axioms Pcf.Examples.Pinched.sqOrbit_injective
#print axioms Pcf.Examples.Pinched.sqStep_surjective
#print axioms Pcf.Examples.Pinched.nodeDivDyn
#print axioms Pcf.Examples.Pinched.nodeDivDyn_branch
#print axioms Pcf.Examples.Pinched.nodeDivDyn_pcSet
#print axioms Pcf.Examples.Pinched.nodeDivDyn_pcf
#print axioms Pcf.Examples.Pinched.pt_four_pow_injective
#print axioms Pcf.Examples.Pinched.pcSet0_infinite
#print axioms Pcf.Examples.Pinched.pcSet1_infinite
#print axioms Pcf.Examples.Pinched.nodeUnnormDyn
#print axioms Pcf.Examples.Pinched.nodeUnnormDyn_not_pcf0
#print axioms Pcf.Examples.Pinched.nodeUnnormDyn_not_pcf1
#print axioms Pcf.Examples.Pinched.nodeUnnormDyn_pcf


-- shared lemmas (formerly Pcf.Stacks.Abhyankar.Tame.ComponentClassification), now in
-- Pcf.Stacks.Abhyankar.StrictComponentClassification and .StrictHeightOneTransport
#print axioms Pcf.Stacks.exists_rootExponent_fractionRing_equiv_of_strictComponent_tame
#print axioms Pcf.Stacks.exists_rootExponent_fractionRing_equiv_of_strictRootComponentData_tame

-- shared (formerly Tame.DVRAbhyankarResidue), now in Pcf.Stacks.Abhyankar.DVRAbhyankarDivisible
#print axioms Pcf.Stacks.maximalIdeal_eq_span_root_of_dvd_and_isSeparable

-- Pcf.Stacks.Abhyankar.Tame.Defs
#print axioms Pcf.Stacks.AbhyankarLemma.of_tame
#print axioms Pcf.Stacks.isUnit_natCast_residueField_iff
#print axioms Pcf.Stacks.mem_minimalPrimes_span_singleton_iff_height_eq_one
#print axioms Pcf.Stacks.isTamelyRamifiedInCodimensionOneAlong_iff

-- shared (formerly Tame.GenericPresentation), now in Pcf.Stacks.Abhyankar.StrictGenericPresentation
#print axioms Pcf.Stacks.exists_strictRootCover_equiv_of_idempotent_factor_tame
#print axioms Pcf.Stacks.isFiniteDisjointUnionOfStandardTameCovers_of_strictlyHenselian_tame

-- shared (formerly Tame.HeightOneUnramified), now in Pcf.Stacks.Abhyankar.StrictHeightOneUnramified
-- and .StrictHeightOneTransport
#print axioms Pcf.Stacks.StrictRootComponentPreData.isUnramifiedAt_of_height_eq_one_of_root_mem_tame
#print axioms Pcf.Stacks.StrictRootComponentPreData.toDataOfDvd_tame_carrier
#print axioms Pcf.Stacks.exists_common_multiple_ramificationIdx_tame
#print axioms Pcf.Stacks.exists_strictRootComponentData_tame

-- shared (formerly Tame.KummerClassification), now in Pcf.Stacks.Abhyankar.KummerNormDescent,
-- .KummerIntermediateEquiv and .StrictComponentClassification
#print axioms Pcf.Stacks.dvrRootFraction_intermediate_eq_power_tame
#print axioms Pcf.Stacks.exists_dvrRootFractionPowerEquiv_of_embedding_tame
#print axioms Pcf.Stacks.exists_dvrRootFractionPowerEquiv_of_embedding_of_isFractionRing_tame

-- Pcf.Stacks.Abhyankar.Tame.RootExponentUnit
#print axioms Pcf.Stacks.isUnit_of_mul_eq_pow_of_not_dvd
#print axioms Pcf.Stacks.isUnit_natCast_localizationAway_of_etale
#print axioms Pcf.Stacks.isUnit_natCast_of_strictRootCover_etale_away

-- shared (formerly Tame.StandardDescent), now in Pcf.Stacks.Abhyankar.StrictStandardConclusion
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.exists_stage_natCast_isUnit
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.exists_pointedEtale_standardTameCover_of_strict_tame
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.hasAbhyankarStandardCoverAt_of_strict_tame

-- Pcf.Stacks.Abhyankar.Tame.StrictBaseChangeTame
#print axioms Pcf.Stacks.comap_algHom_under_eq
#print axioms Pcf.Stacks.isUnramifiedAt_comap_of_etale
#print axioms Pcf.Stacks.algebraMap_mem_map_under_of_etale
#print axioms Pcf.Stacks.residueFieldMapₐOfLiesOver_apply
#print axioms Pcf.Stacks.isUnramifiedAt_residue_of_etale_cover
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.stageToStrictBaseChange_tmul
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.exists_stage_strictBaseChange
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.exists_etale_cover_strictBaseChange
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.module_flat_strictBaseChange
#print axioms Pcf.Stacks.eq_of_le_of_height_eq_one
#print axioms Pcf.Stacks.isTamelyRamifiedAt_of_etale_cover_of_flat
#print axioms Pcf.Stacks.isTamelyRamifiedAt_quotient_idempotent_of_etale_cover
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.isTamelyRamifiedAt_strictBaseChangeFactor

-- Pcf.Stacks.Abhyankar.Tame.Tag0EYGTame
#print axioms Pcf.Stacks.hasAbhyankarStandardCoverAt_of_mem_divisor_tame
#print axioms Pcf.Stacks.abhyankarLemma_tame
#print axioms Pcf.Stacks.abhyankarLemma_of_tame

/-! ## Scheme-level Abhyankar (phase 2, A″, Stacks `0EYG`/`0EYH`)

Every theorem of `Pcf/Stacks/Abhyankar/Scheme/` (list generated from the Lean environment). -/

-- Pcf.Stacks.Abhyankar.Scheme.AffineNormalization
#print axioms Pcf.Stacks.SchemeLevel.baseChange_integralClosure_equiv
#print axioms Pcf.Stacks.SchemeLevel.exists_away_finite_flat_integralClosure
#print axioms Pcf.Stacks.SchemeLevel.exists_away_span_nonZeroDivisor_of_atPrime
#print axioms Pcf.Stacks.SchemeLevel.exists_eq_span_nonZeroDivisor_of_map_eq_span
#print axioms Pcf.Stacks.SchemeLevel.exists_isPrime_tensorProduct_comap_eq
#print axioms Pcf.Stacks.SchemeLevel.exists_radical_eq_span_of_mem
#print axioms Pcf.Stacks.SchemeLevel.exists_span_nonZeroDivisor_atPrime_of_etale
#print axioms Pcf.Stacks.SchemeLevel.finite_flat_away_of_cover
#print axioms Pcf.Stacks.SchemeLevel.integralClosure_finite
#print axioms Pcf.Stacks.SchemeLevel.integralClosure_finite_and_flat
#print axioms Pcf.Stacks.SchemeLevel.integralClosure_flat
#print axioms Pcf.Stacks.SchemeLevel.isReduced_of_etale
#print axioms Pcf.Stacks.SchemeLevel.isRegularLocalRing_atPrime_of_etale
#print axioms Pcf.Stacks.SchemeLevel.isRegularLocalRing_of_flat_of_map_maximalIdeal
#print axioms Pcf.Stacks.SchemeLevel.isRegularRing_quotient_radical
#print axioms Pcf.Stacks.SchemeLevel.pi_mem_nonZeroDivisors
#print axioms Pcf.Stacks.SchemeLevel.pi_span_singleton_eq
#print axioms Pcf.Stacks.SchemeLevel.spanFinrank_le_spanFinrank_map_of_faithfullyFlat
#print axioms Pcf.Stacks.SchemeLevel.stage_reducedDivisor

-- Pcf.Stacks.Abhyankar.Scheme.AffineTame
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.exists_stage_isUnit_natCast
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.exists_stage_localizedStandard
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.hasLocalizedStandardCoverAt_of_stage
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.ker_residueField
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.locStdC_finitePresentation
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.nonempty_localizedStandard_of_algHom
#print axioms Pcf.Stacks.SchemeLevel.hasLocalizedStandardCoverAt_of_tame

-- Pcf.Stacks.Abhyankar.Scheme.AffineTameLocal
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.algebraMap_tensor_tmul
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.comap_map
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.disjoint_primeCompl
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.etale_by
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.finite_integralClosure_of_etale_fractionRing
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.finite_ny
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.instIsScalarTowerAtPrimeBy
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.instIsScalarTowerAtPrimeTensorProductBy
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.isEtaleAt_ny
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.isIntegralClosure_ny
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.isIntegral_tensor
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.isLocalization_away_ny
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.isLocalization_tensor
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.isPrime_map
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.isTamelyRamifiedAt_of_isLocalization

-- Pcf.Stacks.Abhyankar.Scheme.AffineTameTransfer
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.comap_le
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.cp_isScalarTower
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.cp_isScalarTower'
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.hasAbhyankarStandardCoverAt_ny
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.isLocalization_away_fractionRing
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.isLocalization_cp
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.isLocalization_sf
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.isMaximal_map_cp
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.isTamelyRamifiedInCodimensionOneAlong_ny
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.isUnit_ay_by
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.kp_isScalarTower
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.nyToCp_val
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.rp_isLocalization
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.rp_isScalarTower
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.rp_ringKrullDim
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.rpk_isScalarTower
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.sf_algebraMap_tmul
#print axioms Pcf.Stacks.SchemeLevel.AffineTame.sf_isScalarTower

-- Pcf.Stacks.Abhyankar.Scheme.ChartData
#print axioms Pcf.Stacks.SchemeLevel.etale_app_of_etale
#print axioms Pcf.Stacks.SchemeLevel.finite_app_of_isFinite
#print axioms Pcf.Stacks.SchemeLevel.inf_eq_basicOpen_of_ideal_eq
#print axioms Pcf.Stacks.SchemeLevel.isAffineOpen_preimage_ι_of_ideal_eq
#print axioms Pcf.Stacks.SchemeLevel.isLocalization_away_of_ideal_eq
#print axioms Pcf.Stacks.SchemeLevel.isRegularRing_quotient_of_isRegularScheme
#print axioms Pcf.Stacks.SchemeLevel.mem_support_iff_of_ideal_eq

-- Pcf.Stacks.Abhyankar.Scheme.ChartFacts
#print axioms Pcf.Stacks.SchemeLevel.bijective_ι_app_of_le
#print axioms Pcf.Stacks.SchemeLevel.exists_affine_le_complement
#print axioms Pcf.Stacks.SchemeLevel.finite_etale_of_le
#print axioms Pcf.Stacks.SchemeLevel.hasLocalizedStandardCoverAt_chart

-- Pcf.Stacks.Abhyankar.Scheme.Charts
#print axioms Pcf.Stacks.SchemeLevel.exists_etale_pullback_iso_sigma
#print axioms Pcf.Stacks.SchemeLevel.exists_pullback_iso_sigma
#print axioms Pcf.Stacks.SchemeLevel.isIso_sigmaDesc_fin
#print axioms Pcf.Stacks.SchemeLevel.isPullback_fromSpec_app
#print axioms Pcf.Stacks.SchemeLevel.isPullback_tensor_fromSpec
#print axioms Pcf.Stacks.SchemeLevel.mem_basicOpen_iff_notMem_primeIdealOf

-- Pcf.Stacks.Abhyankar.Scheme.Defs
#print axioms Pcf.Stacks.SchemeLevel.abhyankarLemmaTameOver_of_forall
#print axioms Pcf.Stacks.SchemeLevel.abhyankarLemmaTameOver_of_natCast_isUnit
#print axioms Pcf.Stacks.SchemeLevel.abhyankarLemmaTame_of_natCast_isUnit

-- Pcf.Stacks.Abhyankar.Scheme.EffectiveCartier
#print axioms Pcf.Stacks.SchemeLevel.ideal_eq_top_of_disjoint
#print axioms Pcf.Stacks.SchemeLevel.isEffectiveCartier_iff

-- Pcf.Stacks.Abhyankar.Scheme.FiniteEtaleSplitting
#print axioms Pcf.Stacks.SchemeLevel.hasSplitCoverAt_of_finite_etale
#print axioms Pcf.Stacks.SchemeLevel.isFiniteSplit_of_strictlyHenselianLocalRing
#print axioms Pcf.Stacks.SchemeLevel.localColimit_strictlyHenselianLocalRing_of_prime
#print axioms Pcf.Stacks.SchemeLevel.strictlyHenselianLocalRing_of_ringEquiv

-- Pcf.Stacks.Abhyankar.Scheme.IntegralClosureAway
#print axioms Pcf.Stacks.SchemeLevel.isIntegralClosure_localizationAway_integralClosure
#print axioms Pcf.Stacks.SchemeLevel.isLocalization_away_integralClosure

-- Pcf.Stacks.Abhyankar.Scheme.LocalOnTarget
#print axioms Pcf.Stacks.SchemeLevel.bijective_presheaf_map_eqToHom
#print axioms Pcf.Stacks.SchemeLevel.flat_of_iSup_eq_top
#print axioms Pcf.Stacks.SchemeLevel.isFinite_of_iSup_eq_top

-- Pcf.Stacks.Abhyankar.Scheme.NormalizationChart
#print axioms Pcf.Stacks.SchemeLevel.exists_iso_normalization_restrict
#print axioms Pcf.Stacks.SchemeLevel.fst_comp_eq_snd_of_mono
#print axioms Pcf.Stacks.SchemeLevel.ideal_vanishingIdeal_eq_radical
#print axioms Pcf.Stacks.SchemeLevel.isIso_fst_of_mono

-- Pcf.Stacks.Abhyankar.Scheme.ReducedPreimage
#print axioms Pcf.Stacks.SchemeLevel.ideal_radical_comap_eq
#print axioms Pcf.Stacks.SchemeLevel.isEffectiveCartier_radical_comap
#print axioms Pcf.Stacks.SchemeLevel.isRegularScheme_radical_comap

-- Pcf.Stacks.Abhyankar.Scheme.RegularScheme
#print axioms Pcf.Stacks.SchemeLevel.IsAffineOpen.primeIdealOf_fromSpec
#print axioms Pcf.Stacks.SchemeLevel.IsRegularScheme.isLocallyNoetherian
#print axioms Pcf.Stacks.SchemeLevel.IsRegularScheme.isRegularLocalRing_stalk
#print axioms Pcf.Stacks.SchemeLevel.IsRegularScheme.isRegularRing
#print axioms Pcf.Stacks.SchemeLevel.IsRegularScheme.of_isOpenImmersion
#print axioms Pcf.Stacks.SchemeLevel.isRegularLocalRing_stalk_of_isRegularRing
#print axioms Pcf.Stacks.SchemeLevel.isRegularRing_of_isRegularLocalRing_stalk
#print axioms Pcf.Stacks.SchemeLevel.isRegularScheme_iff

-- Pcf.Stacks.Abhyankar.Scheme.StandardRings
#print axioms Pcf.Stacks.SchemeLevel.isStandardTameData_one_one
#print axioms Pcf.Stacks.SchemeLevel.isStandardTameData_unit_mul

-- Pcf.Stacks.Abhyankar.Scheme.Tag0EYG
#print axioms Pcf.Stacks.SchemeLevel.exists_standardTame_of_mem
#print axioms Pcf.Stacks.SchemeLevel.exists_standardTame_of_not_mem
#print axioms Pcf.Stacks.SchemeLevel.tag0EYG
#print axioms Pcf.Stacks.SchemeLevel.tag0EYG_of_affine
#print axioms Pcf.Stacks.SchemeLevel.tag0EYG_of_natCast_isUnit

-- Pcf.Stacks.Abhyankar.Scheme.Tag0EYH
#print axioms Pcf.Stacks.SchemeLevel.exists_rootCover_of_mem
#print axioms Pcf.Stacks.SchemeLevel.exists_rootCover_of_not_mem
#print axioms Pcf.Stacks.SchemeLevel.isRegularRing_of_subsingleton
#print axioms Pcf.Stacks.SchemeLevel.normalization_chart
#print axioms Pcf.Stacks.SchemeLevel.tag0EYH
#print axioms Pcf.Stacks.SchemeLevel.tag0EYH_of_affine
#print axioms Pcf.Stacks.SchemeLevel.tag0EYH_of_natCast_isUnit

-- Pcf.Stacks.Abhyankar.Scheme.TameBridge
#print axioms Pcf.Stacks.SchemeLevel.IsTamelyRamifiedAt.of_ringEquiv
#print axioms Pcf.Stacks.SchemeLevel.IsTamelyRamifiedOver.of_ringEquiv
#print axioms Pcf.Stacks.SchemeLevel.chartTame_of_isTamelyRamifiedInCodimOne
#print axioms Pcf.Stacks.SchemeLevel.isIntegral_map_of_ringEquiv
#print axioms Pcf.Stacks.SchemeLevel.length_quotient_map_ringEquiv
#print axioms Pcf.Stacks.SchemeLevel.natCast_isUnit_residueField_iff
#print axioms Pcf.Stacks.SchemeLevel.ramificationIdx_eq_of_ringEquiv
#print axioms Pcf.Stacks.SchemeLevel.residueField_algebraMap_algebraMap
#print axioms Pcf.Stacks.SchemeLevel.residueField_map_localRingEquiv_algebraMap
#print axioms Pcf.Stacks.SchemeLevel.under_eq_comap_of_ringEquiv

-- Definitions and auxiliary declarations of the scheme-level and tame Abhyankar layers
#print axioms Pcf.Stacks.PointedEtaleNeighborhood.stageToStrictBaseChange
#print axioms Pcf.Stacks.residueFieldMapₐOfLiesOver
#print axioms Pcf.Stacks.SchemeLevel.genericFibreRing
#print axioms Pcf.Stacks.SchemeLevel.integralClosureRingEquiv
#print axioms Pcf.Stacks.SchemeLevel.normalizationAppAlgEquiv
#print axioms Pcf.Stacks.SchemeLevel.specFractionFieldToScheme
#print axioms Pcf.Stacks.SchemeLevel.standardRingOneOneEquiv
#print axioms Pcf.Stacks.SchemeLevel.standardTameRingEquiv
#print axioms Pcf.Stacks.SchemeLevel.standardTameRingOneOneEquiv
#print axioms Pcf.Stacks.StrictRootComponentPreData.toDataOfDvd_tame
