/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Dynamics
import Pcf.Restriction
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

/-!
# Trust audit

`#print axioms` for every headline result of the development, in one place.

**Read `lean/AXIOMS.md` before drawing conclusions from the output below.**
Every line reports only `propext`, `Classical.choice`, `Quot.sound` — the
standard logical axioms of Lean and Mathlib. That is *not* a claim that the
development assumes nothing. The assumed mathematics of the manuscript
(Proposition 4.1, finiteness of the branch divisor, lying over, and the
scheme-theoretic meaning of "prime" and "ramification index") is carried in
*fields* of `Pcf.DivDyn` and `Pcf.PcfSetup` — that is, in hypotheses — and
hypotheses are invisible to `#print axioms` by construction.

The one place where that conditionality is discharged is
`Pcf.Examples.diagonalSquaring`, whose `key` field is proved rather than
assumed; `Pcf.Examples.diagonalSquaring_res_pcf` therefore witnesses that
`Pcf.PcfSetup.res_pcf` is not vacuous.
-/

/-! ## The conjecture the project is named after

Conjecture 2.6 of `latex/pcf.tex` ("PCF all the way down"), due to the authors and quoted
on p. 2 of Bridy–Ingram–Jones–Juul–Levy–Manes–Rubinstein-Salzedo–Silverman, *Finite
ramification for preimage fields of post-critically finite morphisms*, Math. Res. Lett.
**24** (2017), 1633–1647, `arXiv:1511.00194`. Both paragraphs are proved here, in the
abstract layer and conditionally; see `Pcf/AllTheWayDown.lean`. -/

#print axioms Pcf.pcf_periodic_prime
#print axioms Pcf.pcf_all_the_way_down
#print axioms Pcf.pcSet_finite_all_the_way_down

/-! ## §2–§3: divisorial dynamics -/

#print axioms Pcf.DivDyn.IsChain.extend
#print axioms Pcf.DivDyn.exists_isChain_iff
#print axioms Pcf.DivDyn.iterRam_add
#print axioms Pcf.DivDyn.mem_branch_iter_iff
#print axioms Pcf.DivDyn.mem_branch_iter_succ
#print axioms Pcf.DivDyn.pcSet_iter
#print axioms Pcf.DivDyn.pcf_iter_iff
#print axioms Pcf.DivDyn.pcf_iff_forall_orbit_finite
#print axioms Pcf.DivDyn.pcf_of_finite_cover

/-! ## §5: Theorem A and its corollaries -/

#print axioms Pcf.PcfSetup.branch_iter_subset_bound
#print axioms Pcf.PcfSetup.res_pcf
#print axioms Pcf.PcfSetup.res_pcf_of_iter
#print axioms Pcf.PcfSetup.normalization_pcf
#print axioms Pcf.pcf_descent

/-! ## §4 Step 3: the standard tame local model -/

#print axioms Pcf.LocalModel.localPoly_monic
#print axioms Pcf.LocalModel.free
#print axioms Pcf.LocalModel.quotientRootEquiv
#print axioms Pcf.LocalModel.root_mem_nonZeroDivisors

/-! ## §4: the finiteness engine and Zariski–Nagata purity -/

#print axioms Pcf.IsPrime.not_subset_sUnion
#print axioms Pcf.IsPrime.inter_sUnion_ne_self
#print axioms Pcf.not_subset_of_two_le_codim
#print axioms Pcf.finite_isPrime_subset
#print axioms Pcf.PurityData.notMem_nonEtale_of_specializes
#print axioms Pcf.PurityData.codim_eq_one
#print axioms Pcf.PurityData.finite_isPrime_subset_nonEtale

/-! ## §4: Proposition 4.1 -/

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

/-! ## §4→§5: the join -/

#print axioms Pcf.UnramifiedWitness.trivial
#print axioms Pcf.divDynOfGeometry
#print axioms Pcf.PcfGeometry.sing_finite
#print axioms Pcf.PcfGeometry.meets_finite
#print axioms Pcf.PcfGeometry.key
#print axioms Pcf.PcfGeometry.toPcfSetup
#print axioms Pcf.PcfGeometry.res_pcf
#print axioms Pcf.PcfGeometry.res_pcf_of_iter

/-! ## §6: Examples 6.1 and 6.2, and the non-vacuity witness -/

#print axioms Pcf.Examples.squaringP1_branch
#print axioms Pcf.Examples.squaringP1_pcf
#print axioms Pcf.Examples.squaringP1_branch_iter
#print axioms Pcf.Examples.diagonalSquaring_bound
#print axioms Pcf.Examples.diagonalSquaring_res_pcf

/-! ## §4: Examples 4.4 and 4.5 -/

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

/-! ## The purity layer wired into Theorem A

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

/-! ## §7: Example 7.4, the wild counterexample -/

#print axioms Pcf.Examples.CharP.orbit_natDegree
#print axioms Pcf.Examples.CharP.orbit_infinite
