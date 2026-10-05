/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Dynamics
import Pcf.Restriction
import Pcf.Unnormalized
import Pcf.LocalModel
import Pcf.Noetherian
import Pcf.Purity
import Pcf.NonEtaleLocus
import Pcf.ZariskiNagata
import Pcf.Ramification
import Pcf.Abhyankar
import Pcf.Geometry
import Pcf.Wiring
import Pcf.AllTheWayDown
import Pcf.SpectrumDynamics
import Pcf.Examples.Squaring
import Pcf.Examples.CharP
import Pcf.Examples.Cusp
import Pcf.Examples.CofiniteWitness
import Pcf.Examples.Pinched

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

The one place where that conditionality is discharged is
`Pcf.Examples.diagonalSquaring`, whose `key` field is proved rather than
assumed; `Pcf.Examples.diagonalSquaring_res_pcf` therefore witnesses that
`Pcf.PcfSetup.res_pcf` is not vacuous.
-/

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
#print axioms Pcf.Prop41Data.notMem_branch
#print axioms Pcf.Prop41Data.branch_subset_bound
#print axioms Pcf.Prop41Data.finite_bound
#print axioms Pcf.Prop41Data.finite_branch
#print axioms Pcf.Prop41Data.finite_sing_subtype
#print axioms Pcf.Prop41Data.finite_meets_subtype

/-! ## §`sec:bounding`→§`sec:main`: the join -/

#print axioms Pcf.UnramifiedWitness.trivial
#print axioms Pcf.divDynOfGeometry
#print axioms Pcf.PcfGeometry.sing_finite
#print axioms Pcf.PcfGeometry.meets_finite
#print axioms Pcf.PcfGeometry.key
#print axioms Pcf.PcfGeometry.toPcfSetup
#print axioms Pcf.PcfGeometry.res_pcf
#print axioms Pcf.PcfGeometry.res_pcf_of_iter

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

/-! ## Abhyankar's lemma: the standard tamely ramified model

These are the newly discharged half of Stacks Tag 0EYF. The structure theorem
(Tag 0EYG) remains assumed; see `lean/AXIOMS.md`, entry B2. -/

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
