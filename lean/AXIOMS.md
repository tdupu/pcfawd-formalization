# AXIOMS.md — assumed inputs of the Lean formalization

| Field | Value |
| --- | --- |
| Repo | `pcf` |
| Scope | `lean/` |
| Status | Draft |
| Date | `2026-09-21`; §B.8 and the `paper.tex` relabelling added `2026-10-04`; §G (Theorem `thm:bounding` derived) added `2026-10-04` |
| Manuscript | `latex/paper.tex`, cited by `\label` (the file was `pcf.tex` with different numbering when this census was first written; see `HANDOFF.md` §1) |
| Toolchain | Lean `4.34.0`, Mathlib `v4.34.0` (`5ed296525643`) |

This is the *axiom census* of the formalization, in the sense used by the
`gq2` project: the formalization is deliberately **conditional**, and this file
names every input it assumes instead of proving.

## How to read `#print axioms` here

`#print axioms` on every theorem in this development reports only the standard
logical axioms `propext`, `Classical.choice`, `Quot.sound`. **That is not a
claim that nothing is assumed.** The assumed mathematics enters as *fields of
structures* (`Pcf.DivDyn`, `Pcf.PcfSetup`), i.e. as hypotheses, not as Lean
`axiom` declarations — so it is invisible to `#print axioms` by construction.
A theorem of the form `theorem t (h : P) : Q` has no axioms and still proves
only `P → Q`.

There is no `sorry`, no `axiom`, no `admit` and no `native_decide` anywhere in
`lean/Pcf/`. The conditionality is entirely in the list below.

## A. Modelling assumptions (the abstraction itself)

The manuscript is scheme-theoretic. Mathlib has no theory of normal varieties,
normalization, branch divisors, Zariski–Nagata purity or Abhyankar's lemma, so
the development does **not** construct a `DivDyn` from a morphism of schemes.
It axiomatizes the divisorial bookkeeping instead.

| ID | Assumption | Manuscript source |
| --- | --- | --- |
| A1 | The primes of the normalized model of a variety form a type `P`, and a finite dominant self-map induces a *function* `step : P → P` (image of a prime is a prime). | §`sec:intro` Conventions |
| A2 | Ramification indices are captured by a function `ram : P → ℕ` with `ram P' = e(P'/g(P'))`, positive everywhere. | the ramification paragraph before Definition `def:crit-branch` |
| A3 | Branching is modelled by `1 < ram`, i.e. by `e > 1` alone. the ramification paragraph before Definition `def:crit-branch`'s second clause (inseparable residue extension) is **not** modelled. | the ramification paragraph before Definition `def:crit-branch`, Definition `def:crit-branch` and Lemma `lem:dictionary` |
| A4 | The ramification index of the `m`-th iterate equals `∏_{i<m} ram (stepⁱ ·)`. In Lean this is the *definition* of `DivDyn.iterRam`, so multiplicativity of ramification in towers is assumed, not derived. | §`sec:prelim`, proof of Proposition `prop:iterates`(1) |
| A5 | The geometric objects `Sing(X)`, `Sing(A)` and `A ∩ E` are represented by abstract sets of primes (`PcfSetup.sing`, `PcfSetup.meets`). No scheme-theoretic content is attached to them. | Theorem `thm:bounding` |
| A6 | **The chart link** (`Pcf.PcfSetupChart.chart`, §G.4). For every `m ≥ 1`, every prime `Q` of `A` outside `Σₘ` and every `Q'` with `gᵐ(Q') = Q`, there is an affine chart of `fᵐ` around `Q` (a `Pcf.BoundingChart`) with a point `ξ` representing `Q'`, such that `Q' ∈ crit₁(gᵐ)` implies the chart's restriction `R/(a) → S/𝔭` is not étale at `ξ`. This identifies the abstract predicate `crit₁` with non-étaleness computed on charts, and encodes Step 0's choice of `U` avoiding `Σ`. Relative to the derived theorem it is exactly as strong as `key1`; see §G.4. | Theorem `thm:bounding`, Step 0 and Step 4; Definition `def:branch-loci` |

**Consequence.** A3 restricts the development to the characteristic-zero
setting of Theorem `thm:normal-invariant`, where non-étaleness at a source DVR is exactly `e > 1`.
Example `ex:wild` shows that the wild positive-characteristic statement is false, so
nothing is lost for Theorem `thm:normal-invariant` and nothing is claimed beyond it.

## B. Assumed theorems (the interfaces to the literature)

The development has **two layers**, and it matters which one a statement lives in.

* The **abstract layer** (`Pcf/Dynamics.lean`, `Pcf/Restriction.lean`) proves Theorem `thm:normal-invariant`
  from structure fields. It is what §C below describes.
* The **geometric layer** (`Pcf/Noetherian.lean`, `Pcf/Purity.lean`,
  `Pcf/Ramification.lean`, `Pcf/LocalModel.lean`, `Pcf/Geometry.lean`) proves
  Theorem `thm:bounding` and the finiteness statements outright, from strictly smaller inputs.

The two layers **are now joined**. `Pcf.PcfGeometry.toPcfSetup` constructs a
`Pcf.PcfSetup` from geometric data with `sing_finite`, `meets_finite` and `key` **proved**,
and `Pcf.PcfGeometry.res_pcf` is Theorem `thm:normal-invariant` on that route. `Pcf.divDynOfGeometry` likewise
constructs a `Pcf.DivDyn` with `branch_finite'` proved.

So there are three routes to Theorem `thm:normal-invariant`:

* **Abstract route** — `Pcf.PcfSetup.res_pcf` on a hand-built `PcfSetup`. Assumes B1–B5.
* **Geometric route** — `Pcf.PcfGeometry.res_pcf`. Assumes B1 and B2 (they are fields of
  the two `DivDyn`s inside `PcfGeometry`, so they must be supplied twice), P3–P6, and the
  bounding conclusion `key` as an **explicit argument** (since 2026-10-04; it was the field
  P2, equivalent to B5 — see the warning below). What it genuinely no longer assumes is B3
  and B4.
* **Chart route** (2026-10-04, §G) — `Pcf.PcfSetupChart.res_pcf1`. Assumes B1, B2, B3, B4,
  U1–U5, the chart link A6, and **derives** B5/U6 from Zariski–Nagata purity (G1),
  Abhyankar's lemma (G2) and one standard fact (G4, Tag 036W), all stated faithfully to the
  Stacks text; Tags 033B and 01JT are proved (G3, G5).

**A correction, retained.** An earlier version of this file claimed Theorem `thm:bounding` (per-divisor form) is
*proved* from purity and Abhyankar's lemma. It was not.
`Pcf.nonempty_unramifiedWitness_iff` proves that the interface then in use,
`UnramifiedWitness n`, is inhabited exactly when `n = 1`, and that an inhabitant can be
taken to be the identity map `ℤ → ℤ`, with no geometry in it at all. So that interface
carried exactly the conclusion of Theorem `thm:bounding` (per-divisor form), and the step to `notMem_branch` was
a one-line repackaging. The correction was produced by an adversarial review of the
development, retained at `ai/2026-09-21-prop41-formalization/adversarial-review.md`.

**What has since changed, and what has not.** Abhyankar's lemma has two halves, and one
of them is now machine-checked:

* **Assumed** (P2, Stacks Tag 0EYG) — the cover is, étale-locally, a disjoint union of
  standard tamely ramified pieces. Scheme-theoretic; a field.
* **Proved** (Stacks Tag 0EYF, *clauses 1 and 2 only*) — such a piece is finite free, and
  is étale where the divisor equation is invertible: `Abhyankar.finrank`, `Abhyankar.etale`,
  `Abhyankar.ramificationIdx_eq_one`. Clause 3, tameness in codimension one, is not
  stated anywhere. See §B.4.

The interface is now `Pcf.KummerWitness` rather than `Pcf.UnramifiedWitness`.

**This changed nothing about what is assumed.** A second adversarial review proved
`Pcf.kummerWitness_iff_unramifiedWitness`: the two witness types are interderivable,
uniformly in `n`, with no hypotheses and no geometry. An intermediate version of this file
said the assumption had been "shrunk" and that Theorem `thm:bounding` (per-divisor form) was "conditional on
less"; **that is retracted**. The assumption was *restated*, in the same sense in which
§F records that `key` was restated as P2.

The reason is structural. Nothing in `KummerWitness` ties its `Base`, `deg`, `unit` or
`prime` to the prime whose index is `ram q`; the supplier chooses all four freely. So
`Abhyankar.ramificationIdx_eq_one` gets applied to an algebra the supplier invented rather
than to the cover under discussion, and no content crosses. `Pcf.KummerWitness.ofEqOne`
makes the cost explicit: a proof of `n = 1` plus a closed constant, which is exactly what
`UnramifiedWitness` cost.

An intermediate version of this file also argued that equivalence-to-conclusion is
unavoidable for any sufficient interface and therefore not a defect. **That argument is
wrong and is retracted**: a sufficient hypothesis need only *imply* its conclusion. A
genuinely weaker interface is describable — fix the local extension at `q` as data of the
ambient structure and have `standardForm` supply an `AlgEquiv` from that extension onto a
Kummer algebra, so `Algebra.Etale.of_equiv` transports content. That is not what is built.

So: the new material in `Pcf/Abhyankar.lean` is real mathematics, correctly proved, and
**not load-bearing**. *As of 2026-09-21*, Theorem `thm:bounding` (per-divisor form) was
assumed, exactly as before.

**2026-10-04.** The interface `KummerWitness` is no longer a field of anything. Theorem
`thm:bounding` is derived on an affine chart from purity and Abhyankar's lemma in
`Pcf/Bounding/`; see §G, which also records the remaining modelling link A6 and what it is
worth. The paragraphs above are kept as the history that §G answers.

The table below describes what the *structures* demand.

### B.1 Fields of `DivDyn` and `PcfSetup` (what Theorem `thm:normal-invariant` still assumes)

| ID | Lean field | Statement assumed | Now proved elsewhere? |
| --- | --- | --- | --- |
| B1 | `DivDyn.step_surjective` | Lying over: every prime is the image of a prime (proof of Lemma `lem:lift`; Stacks 00HS / 00H8). | **No — still assumed**, but its mathematical content is now proved at the level Mathlib can express it: `Pcf.comap_surjective_of_isIntegral_of_injective` (§B.7). Transporting that to the *divisor* subtype needs image-of-closed-is-closed and codimension preservation, neither of which this development has. |
| B2 | `DivDyn.branch_finite'` | The branch divisor has finitely many components (§`sec:defs`, after Definition `def:crit-branch`). | **Discharged on `Spec S` — see §B.7**, where it costs only lying over and generic étaleness, with no purity input. Partly discharged in the abstract layer — see §B.6. On the new `Pcf.PcfGeometry.ofPurityData` route it is **discharged for the restricted system** from a `Pcf.PurityData`. It remains a field of the *ambient* `amb : DivDyn PX`, which lives on a bare type with no topology, and remains a field on the plain `Pcf.PcfGeometry` and `Pcf.PcfSetup` routes, which still take `res` as a ready-made `DivDyn`. |
| B3 | `PcfSetup.sing_finite` | `Sing(Y) ∩ B` and `Sing(B)` contain finitely many primes (Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many`). | **Genuinely discharged** by `Pcf.PcfGeometry.sing_finite`, from properness plus Noetherianness. |
| B4 | `PcfSetup.meets_finite` | `B ∩ Z` contains finitely many primes (Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many`). | **Genuinely discharged** by `Pcf.PcfGeometry.meets_finite`, from properness plus Noetherianness. |
| B5 | `PcfSetup.key` | **Theorem `thm:bounding` (per-divisor form)**, applied to every iterate. | **Derived on the chart route** (§G, 2026-10-04): `Pcf.PcfSetupChart.key1` proves the étale form from Zariski–Nagata purity and Abhyankar's lemma on charts, through the modelling link A6, and `Pcf.PcfSetup1.toPcfSetup` turns it into `key`. On the abstract route and on `Pcf.PcfGeometry.toPcfSetup` it is an explicit argument. The former `standardForm` (P2) is **removed**. |

### B.2 What the geometric layer actually assumes

These are the irreducible inputs — the statements that are genuinely quoted from the
literature rather than derived.

| ID | Lean field | Statement assumed | Source |
| --- | --- | --- | --- |
| P1 | `PurityData.localPurity` | **More than Stacks Tag 0BMB.** `Pcf.ZariskiNagata` (§B.5) restates the tag with all five hypotheses, but is *interderivable* with this field and so does not reduce it. The field says: if a point has codimension ≥ 1 and the morphism is étale at every codimension-one generization, it is étale there — quantified over *every* such point, with none of 0BMB's hypotheses (1) `𝒪_{X,x}` normal, (2) `𝒪_{Y,y}` regular, (3) `f` quasi-finite at `x`, (4) the dimension equality. Those hold throughout §`sec:bounding`'s application and are absorbed into the field rather than carried as data, so the field is 0BMB *plus* the standing hypotheses of §`sec:bounding`. Separately, substituting "étale at `x'`" for 0BMB's "unramified at `x'`" strengthens the hypothesis and so weakens the implication — that substitution alone is harmless. | Stacks Tag 0BMB plus §`sec:bounding`'s standing hypotheses |
| P2 | *(removed 2026-10-04)* formerly `Prop41Data.standardForm`, `PcfGeometry.standardForm` | **Was Theorem `thm:bounding` (per-divisor form) itself**, phrased as a `Pcf.KummerWitness` at each prime above a good prime, and **logically equivalent to its own conclusion** (`Pcf.nonempty_kummerWitness_iff`, `Pcf.kummerWitness_iff_unramifiedWitness`). Both fields are gone. Their replacement is the pair `Pcf.Stacks.ZariskiNagataPurity` / `Pcf.Stacks.AbhyankarLemma` of §G, which are statements about the cover `R → S` and cannot mention the restriction. The witness types and the refutation theorems remain in `Pcf/Geometry.lean`, consumed by nothing. | Stacks Tags 0EYF, 0EYG; SGA 1 Exp. XIII Prop. 5.2 |
| P3 | `PurityData.closure_eq_univ_of_codim_eq_zero` | A point of codimension zero is a generic point. **Discharged** for `Pcf.purityDataOfAlgebra` (§B.5); still a field of the abstract structure. | Bookkeeping; true in an irreducible scheme |
| P4 | `PurityData.nonEtale_isClosed`, `nonEtale_ne_univ` | The étale locus is open, and the morphism is generically étale (separability). The **first is discharged** for `Pcf.purityDataOfAlgebra` from `Algebra.isOpen_etaleLocus` (§B.5); the second remains assumed. | §`sec:bounding`, and §`sec:defs`'s separability hypothesis |
| P5 | `Prop41Data.singSelf_isClosed`, `singSelf_ne_univ` | `Sing(B)` is a proper closed subset — a variety in characteristic zero is generically regular. | Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many` |
| P6 | `Prop41Data.singAmbient_*`, `interOther_*` | The other two loci are proper closed. For `B ∩ Z` this is **proved** by `Pcf.IsPrime.inter_sUnion_ne_self`; for `Sing(Y) ∩ B` it follows from `Pcf.not_subset_of_two_le_codim` given that `Sing(Y)` has codimension ≥ 2 (normality of `Y`). | Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many` |

**The global form of purity is no longer assumed.** The manuscript derives it from the
local form by hand, remarking that the SGA reference was "difficult to parse for the
present application". That derivation is now machine-checked:
`Pcf.PurityData.codim_eq_one`.

**Non-vacuity of P2.** `Pcf.KummerWitness.cubic` inhabits the witness type, so P2 is not
unsatisfiable-by-construction. That is *all* it shows. Its degree `3` is a free choice —
degree-1 witnesses exist too, and in those the Kummer algebra is the base ring itself, so
the structure map is bijective. And the prime inside `cubic` is produced by
`Ideal.exists_maximal` composed with `Classical.choice`: nothing identifies it, and
nothing excludes the rational point of `ℚ[y]/(y³ − 1)` at which the local extension is
trivial. An intermediate version of this file presented the degree `3` as evidence that
the interface demands something non-trivial; it is not, and that is retracted.

`Pcf.UnramifiedWitness.trivial` and `Pcf.LocalModel.unramifiedWitness` remain in the
development but **are no longer consumed by any field**. They record the manuscript's own
Step 3/4 route (the restriction to the divisor is an isomorphism). In that route the two
`e`s are different quantities — the `e` of the local model is the degree of the *cover*,
while the index parameter is that of the *restriction*, which is `1` in every case.

**Non-vacuity of the join.** `Pcf/Examples/CofiniteWitness.lean` builds a complete
`Pcf.PcfGeometry` over `ℕ` with the cofinite topology, in which
`Pcf.IsPrime s ↔ ∃ x, s = {x}` is proved, the restricted system **genuinely ramifies**
(`resDyn_branch : resDyn.branch = {zeroPrime}` with `ram zeroPrime = 2`), the ramified
prime sits inside a correction locus exactly as Theorem `thm:bounding` permits, and `res.PCF` is
obtained by *applying* `Pcf.PcfGeometry.res_pcf`. So the join is not vacuous.

That witness is deliberately cheap in one respect, and the file says so: because its
restricted system is the identity with `ram ≡ 1` away from the ramified prime, its
`standardForm` is discharged by `Pcf.KummerWitness.cubic` — transported along a proof that
the index is `1`, via `Pcf.KummerWitness.ofEqOne` — and exercises **no** purity or
Abhyankar content. It establishes consistency and inhabitation of `PcfGeometry`, not the
geometric substance. `CofNat` is a toy space, not a variety.

## B.3 A trap this layer closes

An independent check of this development produced the following, as a purported
counterexample to Step 3:

> Take `R = ℤ`, `a = 2`, `u = 1`, `e = 2`, so `C = ℤ[√2]` and `z = √2`. Then
> `C/(z) ≅ ℤ/2 ≅ R/(a)`, yet `2` is totally ramified in `ℤ[√2]`: `(2) = (√2)²`,
> ramification index `2`.

The computation is correct, and it refutes the claim "the two quotient *rings* are
isomorphic, therefore the ramification index is 1" — a claim the manuscript never makes.
Step 4 is about the **restriction** `g = f|_A`, whose local model is the specific map
`R/(a) → C/(z)`; the *cover* `R → C` really is ramified with index `e`, and the manuscript
says so.

The formalization now pins both halves so the confusion cannot recur:

* `Pcf.LocalModel.restrictionMap_bijective` — the named map `R/(a) → C/(z)` is bijective.
  This, not the abstract isomorphism `quotientRootEquiv`, is what Step 4 consumes.
* `Pcf.LocalModel.root_ne_zero_mod_algebraMap` — under `2 ≤ e`, `Nontrivial R` and
  `¬ IsUnit a`, the class of `z` in `C ⧸ (a)` is a **nonzero** nilpotent, so the fibre of
  the cover over the divisor is genuinely non-reduced. This is the ramification direction,
  and it is proved.

  An earlier version of this file pointed instead at
  `Pcf.LocalModel.isNilpotent_root_mod_algebraMap`, which was wrong: that lemma carries no
  hypothesis on `e`, holds at `e = 0` and `e = 1`, and at `e = 1` exhibits the nilpotent
  `0`, since `z = ua` there. A statement true of the unramified case is not evidence of
  ramification. The adversarial review caught this; the three hypotheses above are what it
  takes to exclude those cases.

  Note what is still *not* proved: that the ramification index of the cover is exactly `e`.
  Non-reducedness of the fibre is weaker than that, and nothing here computes the index.

## B.4 Stacks Tag 0EYF: which clauses are proved, and what they are worth

`lean/Pcf/Abhyankar.lean` imports nothing outside Mathlib. Tag 0EYF makes three
assertions about `C = A[x]/(x^e − f)`; this file addresses two.

| Tag 0EYF clause | Status | Lean declaration |
| --- | --- | --- |
| 1. `Spec(C) → Spec(A)` finite locally free | **proved**, as free of rank `e` | `Abhyankar.finrank`; freeness and finiteness are Mathlib's `Polynomial.Monic.free_adjoinRoot` / `Monic.finite_adjoinRoot` |
| 2. étale over `Spec(A_f)` | **proved** | `Abhyankar.etale`, `Abhyankar.ramificationIdx_eq_one`, `Abhyankar.etale_ramifiedPoly_general` |
| 3. tamely ramified over `Spec(A)` in codimension 1 | **not proved, not stated** — no tameness predicate, no codimension, no `Spec(A)` in the file | — |

Clause 3 is what the name "standard *tamely ramified* morphism" refers to, and it is the
clause the proof of Tag 0EYG consumes.

Supporting results:

| Statement | Lean declaration |
| --- | --- |
| the Bézout identity `f' · p₁ + f · p₂ = 1` for `f = X^e − u` | **Mathlib's** `Polynomial.separable_X_pow_sub_C_unit` (this is `Polynomial.Separable`, which unfolds to `IsCoprime f (derivative f)`) |
| monic + separable ⟹ standard étale root algebra | `Abhyankar.isStandardEtale_adjoinRoot_of_separable` — **the general form**, and the one genuine library gap found |
| `R[y]/(y^e − u)` is a standard étale `R`-algebra | `Abhyankar.isStandardEtale` |
| it is nontrivial and has primes | `Abhyankar.nontrivial_adjoinRoot`, `Abhyankar.exists_isPrime` |
| **tameness is necessary** — in characteristic 2 with `e = 2` the conclusion fails | `Abhyankar.not_etale_wild` |
| **the unit hypothesis is necessary** — at `a = 0` the model `k[y]/(y^e)` is not reduced | `Abhyankar.not_etale_of_not_isUnit` |
| the substitution `x ↦ t·y`, an isomorphism when `t` is a unit | `Abhyankar.subst`, `Abhyankar.substEquiv` |

Two cautions about the table above.

* **`substEquiv` is not Tag 0EYF.** It assumes the divisor equation is already `t^e` for a
  unit `t` — a perfect `e`-th power. Inverting `f` makes it a unit, not an `e`-th power;
  making it an `e`-th power is the extra base change performed inside the proof of Tag
  0EYG. An intermediate version of this file sourced `Abhyankar.etale_ramifiedPoly` to
  "Tag 0EYF, `Spec(C_f) → Spec(A_f)`"; that is wrong and is corrected. The statement that
  does correspond to inverting `f` is `Abhyankar.etale_ramifiedPoly_general`, which needs
  no `e`-th power hypothesis. Nothing in the development consumes either.
* **`Abhyankar.ramificationIdx_eq_one` is about Mathlib's `Ideal.ramificationIdx`**, a
  `Module.length`. Identifying that with the ramification paragraph before Definition `def:crit-branch` of the manuscript is listed in §E
  as not formalized, and it remains not formalized. the ramification paragraph before Definition `def:crit-branch`'s index is for the DVR
  of the *divisor prime* and for the *restriction* `g = f|_A`; the Lean index here is over
  a base with the divisor equation inverted, and is the *cover's*.

**What this is worth to the development: standalone mathematics, still not load-bearing.**
The derivation of Theorem `thm:bounding` in `Pcf/Bounding/` (§G) does not go through
`Pcf/Abhyankar.lean`: Steps 3–4 use `Pcf.LocalModel` (the restriction of a standard piece to
the divisor is an isomorphism), which holds for any `e ≥ 1`, and tameness is consumed only
inside the assumed `Pcf.Stacks.AbhyankarLemma`. The remark that a genuinely weaker interface
would "fix the local extension as data and have Abhyankar's lemma supply an `AlgEquiv` from
that extension" is what §G now does: the extension is the chart's `R → S`, and G2 supplies
`R' ⊗[R] S ≃ₐ[R'] ∏ R'[zᵢ]/(zᵢ^{eᵢ} − uᵢ a)` for it.

## B.5 Zariski–Nagata purity: two fields discharged, and the tag stated faithfully

`lean/Pcf/NonEtaleLocus.lean` and `lean/Pcf/ZariskiNagata.lean` address entries P1, P3 and
P4. **Purity itself is still assumed** — Mathlib does not have it — but two of the four
fields of `Pcf.PurityData` become theorems once the abstraction is instantiated at the
spectrum of an actual algebra, and the assumed field is restated so that it matches Stacks
Tag 0BMB instead of exceeding it.

### Discharged

| Field | Was | Now | Why |
| --- | --- | --- | --- |
| `nonEtale_isClosed` (part of P4) | assumed | **proved** for `Pcf.purityDataOfAlgebra` | `Algebra.isOpen_etaleLocus`: Mathlib proves the étale locus is open, so its complement is closed |
| `closure_eq_univ_of_codim_eq_zero` (P3) | assumed | **proved** for `Pcf.purityDataOfAlgebra` | over a domain a prime of height zero is `⊥`, and `V(⊥) = Spec S` |

Both are consumed by the manuscript's own deduction:
`Pcf.PurityData.notMem_nonEtale_of_specializes` uses the first and
`Pcf.PurityData.one_le_codim` uses the second. So within the purity layer these are real
discharges, not decoration.

The truncation `Pcf.specCodim p = (p.asIdeal.height).toNat` from `ℕ∞` to `ℕ` is a junk-value
hazard — a prime of infinite height would read as codimension zero — so
`Pcf.purityDataOfAlgebra` takes finiteness of heights as an explicit hypothesis rather than
hiding it behind Noetherianness.

### Not made faithful — a retraction

`Pcf.ZariskiNagata` states Tag 0BMB with all five of its hypotheses present, and
`Pcf.PurityData.ofZariskiNagata` derives `localPurity` from it plus four standing
hypotheses. An earlier version of this section claimed that this made P1 match the
literature instead of exceeding it, and that "the assumption is now exactly the cited
theorem".

**That is false and is retracted.** The hypothesis fields `normal`, `regularBelow`,
`quasiFinite` are bare `X → Prop` and `codimTarget` a bare `X → ℕ`, tied to no morphism,
no local ring and no scheme. `Pcf.PurityData.toZariskiNagata` therefore builds a
`ZariskiNagata` from *any* `PurityData` by instantiating them at `True`, and
`Pcf.PurityData.ofZariskiNagata_toZariskiNagata` proves the roundtrip is the identity —
**definitionally**; the proof is `cases D; rfl`. The two are interderivable, so nothing was
reduced.

This is the third time in this repository that an interface decorated with content-free
predicates has been presented as an axiom reduction. The first two were
`Pcf.UnramifiedWitness` and `Pcf.KummerWitness` (§B.2). The corresponding refutations are
now all stated as Lean theorems: `Pcf.nonempty_unramifiedWitness_iff`,
`Pcf.kummerWitness_iff_unramifiedWitness`, and
`Pcf.PurityData.ofZariskiNagata_toZariskiNagata`.

A related claim is also retracted: the docstring of `ofZariskiNagata` said requiring the
standing hypotheses at every point was "much less than the previous field, which required
none of them". By the roundtrip it is *exactly* the previous field. Its `hdim` field
additionally asks for global equidimensionality, which is **more** than §`sec:bounding` uses.

What the structure is actually worth: a caller holding genuine normality, regularity and
quasi-finiteness predicates can state the tag with them rather than absorbing them
silently. That is expressive value, not a theorem.

### A sharper fact, found by the same review

`Pcf.localPurity_of_codim_le_one` proves that the `localPurity` field holds **for free**
when every point of the non-étale locus has codimension at most one, because `Specializes`
is reflexive and the field's own hypothesis applied at the point itself closes the goal.

So all of the content of Tag 0BMB, as this development uses it, lies at points of
codimension at least two — which is exactly where the manuscript applies it
(`Pcf.PurityData.notMem_nonEtale_of_specializes` assumes `2 ≤ codim η`).
`Pcf.PurityData.ofCodimLeOne` packages this.

A practical consequence, not yet exploited: a non-degenerate example with `E ≠ ∅` but `E`
of pure codimension one would need **no purity input at all**. The only obstacle to
building one is computing a non-étale locus in Mathlib, not purity.

### Not discharged, and not claimed

* **Purity itself** (`ZariskiNagata.purity`, Stacks Tag 0BMB) is a field. Nothing here
  proves any part of it.
* **`nonEtale_ne_univ`** — generic étaleness — remains a hypothesis. In the manuscript it
  is the separability of the function-field extension; it is a real condition on `S`.
* **Non-vacuity is degenerate.** `Pcf.purityDataOfEtale` inhabits the datum, but only with
  `E = ∅`, where there are no components of `E` and `Pcf.codim_eq_one_of_algebra` has no
  instances. No example with `E ≠ ∅` is built, so global purity is not exercised
  non-trivially on any concrete algebra.
* **`Pcf.PurityData` was not consumed by Theorem `thm:normal-invariant` when §B.5 was written.** It is now, via
  `Pcf/Wiring.lean`; see §B.6 for exactly how much that buys and how much it does not.
* **The two new files do not talk to each other.** `Pcf/NonEtaleLocus.lean` does not
  import `Pcf/ZariskiNagata.lean`, and `Pcf.purityDataOfAlgebra` takes the plain
  `localPurity`-shaped hypothesis, not a `Pcf.ZariskiNagata`. Nothing outside
  `Pcf/ZariskiNagata.lean` references that structure except the audit. They are two
  separate pieces of work on the same layer, not a chain.

## B.6 The purity layer wired into Theorem `thm:normal-invariant`

`lean/Pcf/Wiring.lean` is the first place in this development where the purity layer
reaches Theorem `thm:normal-invariant`. Before it, §B.5's discharges improved a side branch;
`Pcf.divDynOfGeometry` existed but nothing was built through it.

### The chain

| Step | Status |
| --- | --- |
| `Algebra.isOpen_etaleLocus` | Mathlib |
| ⟹ `Pcf.isClosed_nonEtaleLocus` | proved (§B.5) |
| ⟹ `Pcf.finite_isPrime_subset` | proved, needs Noetherian |
| ⟹ `DivDyn.branch_finite'` for the restricted system | **proved** — `Pcf.resDivDynOfPurity` |
| ⟹ `Pcf.PcfGeometry.res_pcf` | proved |

Each arrow is a theorem. That is **not** the claim that nothing is assumed: the inputs —
generic étaleness (`nonEtale_ne_univ`), purity itself (`localPurity`),
`ramified_subset_nonEtale`, and `standardForm` — are all still hypotheses. What changes is
that `branch_finite'` is no longer among them on this route.

`Pcf.resDivDynOfAlgebra` is the composite over an honest `R`-algebra, and takes **no
closedness argument**: Mathlib supplies it.

### Exactly what is and is not discharged

* **Discharged:** `branch_finite'` for the **restricted** system `res`, on the
  `Pcf.PcfGeometry.ofPurityData` route.
* **Still assumed:** `branch_finite'` for the **ambient** system `amb`. It is a field of
  `amb : DivDyn PX`, and `PX` is a bare type with no topology, so there is nothing to run
  the argument on.
* **Still assumed:** `branch_finite'` on the plain `Pcf.PcfGeometry` and `Pcf.PcfSetup`
  routes, which take `res` as a ready-made `DivDyn`. The field was not removed from the
  structure; an alternative constructor was added that does not need it.

### The trade, and its converse

`branch_finite'` is exchanged for `ramified_subset_nonEtale` (ramified primes lie in the
non-étale locus — Definition `def:crit-branch` in the direction the argument needs), plus properness of
that locus, plus Noetherianness.

**This is a trade, not a reduction in logical strength**, and
`Pcf.exists_nonEtale_of_branch_finite` proves the converse: given `branch_finite'`, the
union of the finitely many branch primes is a closed set with the required property, so
the trade reverses as soon as that union is not the whole space. Three earlier tasks in
this repository claimed reductions that were not reductions (§B.2, §B.5); the converse is
stated here so that this one cannot be read as a fourth.

What the trade is worth: the hypothesis it introduces is the one the manuscript actually
states, and one of its three components — closedness — is now supplied by Mathlib instead
of assumed.

### Non-vacuity

`Pcf.Examples.resDynOfPurity` is an inhabitant with **genuine ramification**:
`resDynOfPurity.branch = {zeroPrime}`, and `Pcf.Examples.resDynOfPurity_pcf` obtains
`PCF` by *applying* `Pcf.PcfGeometry.res_pcf_of_purityData`. Its `branch_finite'` is
proved, not supplied.

Two caveats the file itself records. Its purity datum is built by
`Pcf.PurityData.ofCodimLeOne`, so `localPurity` costs nothing there (§B.5) and no
Zariski–Nagata content is exercised; and its closedness comes from the singleton `{0}`
being finite, not from `Algebra.isOpen_etaleLocus`. It exercises the *finiteness* half of
the wiring. The Mathlib half is exercised by `Pcf.resDivDynOfAlgebra`, whose only
available instances have an unramified restricted system, because the sole inhabitant of
the spectrum route so far is `Pcf.purityDataOfEtale` with `E = ∅`.

## B.7 `branch_finite'` fully discharged on `Spec S`

§B.6 derived `DivDyn.branch_finite'` for a restricted system from a `Pcf.PurityData`, but
still assumed `ramified_subset_nonEtale`. `lean/Pcf/SpectrumDynamics.lean` removes that
too, and more besides. The comparison is the clearest way to state it:

| Input | `Pcf.resDivDynOfPurity` (§B.6) | `Pcf.divDynOfSpectrum` |
| --- | --- | --- |
| `step`, `step_surjective` (lying over, B1) | supplied | supplied |
| `ram` | **supplied by the caller** | canonical — `Ideal.ramificationIdx` at the generic point |
| `ram_pos` | **supplied** | **proved** (`Ideal.ramificationIdx_pos`) |
| ramified ⟹ non-étale | **supplied** (`hbranch`) | **proved** |
| a `Pcf.PurityData`, including `localPurity` = Tag 0BMB | **required** | **not required at all** |
| generic étaleness | a field of the datum | the one remaining hypothesis |
| `branch_finite'` (B2) | derived | derived |

So on this route a `Pcf.DivDyn` over `Spec S` costs exactly two assumptions: **lying over**
and **`nonEtaleLocus R S ≠ univ`** (the separability hypothesis of §`sec:defs`). Zariski–Nagata is
not among them — `branch_finite'` never needed purity, only closedness of the locus,
properness, and Noetherianness.

### The two new theorems

* `Pcf.mem_nonEtaleLocus_of_one_lt_ramificationIdx` — **ramified implies non-étale.** From
  `Ideal.ramificationIdx_eq_one`, which derives index `1` from unramifiedness, together
  with "étale implies unramified". This is Definition `def:crit-branch` in the direction §`sec:bounding` uses it, and
  it was previously a hypothesis on every route.
* `Pcf.subset_nonEtaleLocus_of_one_lt_specRam` — the same statement for a whole prime
  rather than a point. `PrimeSpectrum` is sober, so a prime is the closure of its generic
  point, and the locus is closed.

### Is this another restatement? No, and here is the check

The three earlier failures (§B.2, §B.5) were interfaces logically equivalent to their own
conclusions. This one is not, and the reason is structural: the surviving hypothesis
`nonEtaleLocus R S ≠ univ` mentions only `R` and `S`. It refers to no `step`, no `ram` and
no branch set, so no field of `Pcf.DivDyn` can imply it and the derivation cannot be
circular. The content that replaced `hbranch` is a Mathlib theorem, not a new field.

### Lying over, proved at the point level

`Pcf.comap_surjective_of_isIntegral_of_injective` proves Stacks Tag 00HS: for an injective
integral ring map the induced map on prime spectra is surjective. That is the content of
B1, from `Ideal.nonempty_primesOver`.

**It does not discharge the field.** `DivDyn.step_surjective` is about a self-map of
*divisors*, elements of `{s : Set (PrimeSpectrum S) // IsPrime s}`. Transporting the point
statement there needs (i) the image of a closed set under a finite morphism is closed and
(ii) that such a morphism preserves codimension. (ii) is dimension theory Mathlib's Krull
API does not currently reach. So B1 stands, with its content identified and proved where it
can be.

This is exactly the same shape as the `hbranch` discharge above, which *did* go through —
the difference is that there the transport was by generic points into a *closed* set, which
costs nothing, whereas here it needs a dimension statement.

### What it does not do

* **It does not prove purity**, and does not reduce P1. No `PurityData` is involved.
* **It does not discharge B1**, only identifies and proves its content on points.
* **It does not touch Theorem `thm:bounding` (per-divisor form)**, `standardForm` or `PcfSetup.key`.
* **A1 stands.** `step` is an arbitrary self-map of the primes of `Spec S`, connected to no
  morphism of schemes. Lying over is still assumed rather than derived from one.
* **A2 improves but §E still stands.** `ram` is now *definitionally* Mathlib's
  `Ideal.ramificationIdx` rather than an abstract `ℕ`-valued function, which is a real gain
  in concreteness — but the identification of that index with the ramification paragraph before Definition `def:crit-branch`'s
  `e(𝔮/𝔪)` is still not formalized, exactly as §E records.
* **Non-vacuity is weak.** `Pcf.divDynOfSpectrum` is inhabited (checked, with `R = S = ℚ`),
  but no instance with a genuinely ramified prime is exhibited; that needs a concrete
  ramification-index computation which Mathlib does not make easy.

## B.8 The unnormalized loci: fields of `Pcf.UnnormDyn` and `Pcf.PcfSetup1`

Added 2026-10-04 for Appendix `app:other-defs` and the `1`-PCF form of Theorem
`thm:normal-invariant`. `Pcf/Unnormalized.lean` extends `DivDyn` by two critical predicates
`crit0 m`, `crit1 m` (for `crit₀(gᵐ)`, `crit₁(gᵐ)` of Definition `def:branch-loci`) and the
following **assumed** fields. All five are scheme-level statements proved in the manuscript
from Kähler differentials and Stacks Tags 02GF, 02GW, 02GN, 04HH, 07TD; none is in reach of
this layer, which has no morphism of schemes.

| ID | Lean field | Statement assumed | Manuscript source |
| --- | --- | --- | --- |
| U1 | `UnnormDyn.crit_subset_crit0` | `e(Q/gᵐ(Q)) > 1 ⟹ Q ∈ crit₀(gᵐ)`, for every `m` | `prop:loci-compare`(2), first inclusion |
| U2 | `UnnormDyn.crit0_subset_crit1` | `crit₀(gᵐ) ⊆ crit₁(gᵐ)` | `prop:loci-compare`(2), second inclusion |
| U3 | `UnnormDyn.crit1_finite` | `crit₁(gᵐ)` has finitely many components | `prop:loci-compare`(1) |
| U4 | `UnnormDyn.crit0_tower` | `crit₀(g) ⊆ crit₀(gⁿ⁺¹)` | `lem:tower-unnormalized`(1) with `h = gⁿ` |
| U5 | `UnnormDyn.crit1_tower` | `Q ∈ crit₁(g) ⟹ Q ∈ crit₁(gⁿ⁺¹) ∨ g(Q) ∈ crit₁(gⁿ)` | `lem:tower-unnormalized`(2) with `h = gⁿ` |
| U6 | `PcfSetup1.key1` | the **étale** conclusion of `thm:bounding` for `fᵐ`, every `m ≥ 1`: a prime of `A` outside `Σ_m` is not in `branch₁(gᵐ)` | `thm:bounding` |

U6 is the new primitive of the manuscript. It is *stronger* than B5 (`PcfSetup.key`), and
`Pcf.PcfSetup1.toPcfSetup` derives B5 from U6 and U1–U2; so the `PcfSetup1` route assumes
U6 in place of B5, not in addition to it. `key1` is stated only for `m ≥ 1`; the `m = 0`
case of `key` is proved from `iterRam 0 = 1`.

**U6 is derived on the chart route** (§G, 2026-10-04): `Pcf.PcfSetupChart.key1` proves it from
Zariski–Nagata purity and Abhyankar's lemma on charts, given the modelling link A6 and the
standard fact G4 (Tag 036W; G3 and G5 are proved). `Pcf.PcfSetup1` keeps `key1` as a field so
that the abstract route and the examples are unchanged; `Pcf.PcfSetupChart.toPcfSetup1` fills
it.

### Modelling caveats specific to this layer

* **One carrier for two kinds of prime.** `crit₀`, `crit₁` are sets of primes of `A`
  *itself*; `ram` is the index on the normalization `Ã` (assumption A1). The structure puts
  both on the same type `P`. For `A` regular in codimension one (in particular normal) the
  primes of `A` and of `Ã` correspond bijectively and the identification is exact. For
  non-normal `A` — the case `ex:pinched` is about — `ν` is finite-to-one and a prime of `A`
  may carry several indices; `nodeDivDyn` in `Pcf/Examples/Pinched.lean` resolves this by
  taking `ram` at the node to be `1`, the common value at both primes above it, and the
  file's header says so. The existing `PcfSetup.sing`/`meets` make the same identification.
* **`crit_i(gᵐ)` is data, not derived.** There is no formula for `crit₀(gᵐ)` in terms of
  `crit₀(g)` (the manuscript proves only inclusions), so each iterate's locus is a separate
  input, constrained only by U1–U5.
* **Only the instance `h = gⁿ` of `lem:tower-unnormalized` is assumed**, which is all
  `cor:orbit-unnormalized` and `thm:normal-invariant` use. The lemma's inclusions of branch
  loci for a general tower `h ∘ g`, and the failure of the converse inclusions, are not stated.
* **`prop:loci-compare`(3)** (agreement of the three loci where both local rings are
  normal) is not stated.

### What is proved from U1–U6

`Pcf.UnnormDyn.orbit_unnormalized_zero/one` (`cor:orbit-unnormalized`),
`Pcf.UnnormDyn.pcf1_of_branch1_subset` (the dynamical half of `thm:normal-invariant`),
`Pcf.UnnormDyn.pcf0_of_pcf1`, `Pcf.UnnormDyn.pcf_of_pcf0` (`1`-PCF ⟹ `0`-PCF ⟹ PCF),
`Pcf.PcfSetup1.res_pcf1` (`thm:normal-invariant`), `Pcf.PcfSetup1.res_pcf0/res_pcf`
(`cor:normal-invariant-pcf`), `Pcf.PcfSetup1.res_pcf1_of_iter` (`cor:normal-preperiodic`).

### `ex:pinched`

`Pcf/Examples/Pinched.lean` proves the ring-level claims outright (any commutative ring for
`f̃*R ⊆ R` and `R_B` closed under `p ↦ p(z²)`; a field of characteristic zero, using only
`4 ≠ 0`, for `R = k[w, z², z(w−1), z³−4z]`; characteristic zero for the injectivity of the
orbit `4, 16, 256, …`). The dynamical conclusion — `PC₀(g)` and `PC₁(g)` infinite while
`PC(g) = {0}` — is proved for **any** `UnnormDyn` on the points of `B` with step `z ↦ z²`
and `o ∈ crit₀(g)` (`pcSet0_infinite`), and instantiated by `nodeUnnormDyn`, whose critical
loci `{o, 0}` are **stipulated**, not computed. The manuscript's fibre-length argument for
`o ∈ crit₀(g)` (`ℓ(𝒪_{B,o}/g*t) = 2`), the Ferrand pushout, the normalization `ν`, the
finiteness of `f`, and the non-flatness of `f` at `o` are not formalized.

## C. What is proved outright (no assumption beyond A, B and U)

The conjecture the project is named after — Conjecture `conj:pcfawd` of `latex/paper.tex`, due to the
authors and quoted on p. 2 of Bridy–Ingram–Jones–Juul–Levy–Manes–Rubinstein-Salzedo–Silverman,
*Finite ramification for preimage fields of post-critically finite morphisms*, Math. Res.
Lett. **24** (2017), no. 6, 1633–1647, `arXiv:1511.00194` — has **both** of its paragraphs
proved in this layer. See `lean/Pcf/AllTheWayDown.lean`, and read its header for the
conditionality: these are theorems about `Pcf.DivDyn` and `Pcf.PcfSetup`, not about
varieties, and Theorem `thm:bounding` (per-divisor form) is assumed (P2).


Everything in `Pcf/Dynamics.lean` and `Pcf/Restriction.lean`:

| Manuscript | Lean declaration |
| --- | --- |
| Lemma `lem:lift` (padding) | `Pcf.DivDyn.IsChain.extend` |
| chains ↔ iterates dictionary | `Pcf.DivDyn.exists_isChain_iff` |
| multiplicativity in towers | `Pcf.DivDyn.iterRam_add` |
| Proposition `prop:iterates`(1) | `Pcf.DivDyn.mem_branch_iter_iff` |
| Proposition `prop:iterates`(2) | `Pcf.DivDyn.mem_branch_iter_succ` |
| Proposition `prop:iterates`(3)–(4) | `Pcf.DivDyn.pcSet_iter`, `Pcf.DivDyn.pcf_iter_iff`, `Pcf.DivDyn.branch_iter_subset_pcSet`, `Pcf.DivDyn.step_image_pcSet_subset` |
| Definition `def:pcf`, last clause | `Pcf.DivDyn.pcf_iff_forall_orbit_finite` |
| Lemma `lem:normalization` | `Pcf.DivDyn.pcf_of_finite_cover` |
| Theorem `thm:normal-invariant` = Theorem `thm:normal-invariant` | `Pcf.PcfSetup.res_pcf` |
| uniformity of `Σ` in `m` (the crux) | `Pcf.PcfSetup.branch_iter_subset_bound` |
| Corollary `cor:normal-preperiodic` | `Pcf.PcfSetup.res_pcf_of_iter` |
| Corollary `cor:pcfawd`, normalized form | `Pcf.PcfSetup.normalization_pcf` |
| Corollary `cor:pcfawd`, descent (**"PCF all the way down"**, Conjecture `conj:pcfawd` second paragraph) | `Pcf.pcf_descent`, restated as `Pcf.pcf_all_the_way_down` |
| Corollary `cor:normal-preperiodic` (Conjecture `conj:pcfawd` first paragraph) | `Pcf.PcfSetup.res_pcf_of_iter`, restated as `Pcf.pcf_periodic_prime` |

And, in the geometric layer, all of §`sec:bounding` except P1–P6:

| Manuscript | Lean declaration |
| --- | --- |
| the integral-effective-divisor convention of §`sec:intro` (prime), topologically | `Pcf.IsPrime` — **correct only in an irreducible ambient space.** In any space, "no irreducible closed set strictly between `P` and `X`" is exactly codimension one; but `Pcf.IsPrime` is stated for an arbitrary space, where it also holds of the irreducible *components*, which have codimension zero. `IrreducibleSpace` is never assumed. A variety is irreducible by the manuscript's Conventions, so this is a fidelity gap in the abstraction, not an error. |
| primes are incomparable | `Pcf.IsPrime.eq_of_subset_of_isPrime` |
| Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many`, the `Z` term | `Pcf.IsPrime.not_subset_sUnion`, `Pcf.IsPrime.inter_sUnion_ne_self` — *available, not wired in*: `Prop41Data` still takes `interOther_ne_univ` as a field |
| Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many`, the `Sing(Y)` term | `Pcf.not_subset_of_two_le_codim` — *available, not wired in*, and weaker than it looks: `codim` there is an arbitrary `X → ℕ` unconnected to `IsPrime` or to the topology, so it also needs "`B` has codimension 1", which `IsPrime` does not supply. The two notions cannot currently be composed. |
| Theorem `thm:bounding` (per-divisor form), first paragraph (finiteness) | `Pcf.finite_isPrime_subset` |
| §`sec:defs`, finiteness of `Branch(g)` | `Pcf.PurityData.finite_isPrime_subset_nonEtale`; wired in through `Pcf.resDivDynOfPurity` (§B.6), and **fully discharged** over `Spec S` by `Pcf.divDynOfSpectrum` (§B.7) |
| Definition `def:crit-branch`, ramified ⟹ non-étale | `Pcf.mem_nonEtaleLocus_of_one_lt_ramificationIdx` — **proved** from `Ideal.ramificationIdx_eq_one`; previously a hypothesis (§B.7) |
| the converse trade | `Pcf.exists_nonEtale_of_branch_finite` — a **negative** result (§B.6) |
| §`sec:bounding`, purity: local form ⟹ global form | `Pcf.PurityData.codim_eq_one`. `Pcf.codim_eq_one_of_algebra` and `Pcf.ZariskiNagata.codim_eq_one` are *restatements* of it at a spectrum and through `ZariskiNagata`; no result combines them |
| the étale locus is open ⟹ `E` is closed | `Pcf.isClosed_nonEtaleLocus` — **discharges a field** of `PurityData`, which is itself not consumed by Theorem `thm:normal-invariant` (§B.5) |
| height-zero points are generic | `Pcf.closure_eq_univ_of_specCodim_eq_zero` — same status |
| purity is free below codimension two | `Pcf.localPurity_of_codim_le_one` |
| the `ZariskiNagata`/`PurityData` roundtrip is the identity | `Pcf.PurityData.ofZariskiNagata_toZariskiNagata` — a **negative** result (§B.5) |
| §`sec:bounding`, the inner maximality step | `Pcf.PurityData.notMem_nonEtale_of_specializes` |
| Theorem `thm:bounding`, Step 3 (as a *map*) | `Pcf.LocalModel.restrictionMap_bijective` |
| Stacks Tag 0EYF, clauses 1–2 only | `Abhyankar.finrank`, `Abhyankar.etale`, `Abhyankar.ramificationIdx_eq_one`, `Abhyankar.etale_ramifiedPoly_general` — see §B.4. **Not consumed by any assumption of the development.** |
| necessity of both hypotheses of Tag 0EYF(2) | `Abhyankar.not_etale_wild`, `Abhyankar.not_etale_of_not_isUnit` |

| Theorem `thm:bounding`, Step 4's final inference | `Pcf.Ramification.ramificationIdx_eq_one_of_bijective`, `Pcf.UnramifiedWitness.eq_one` |
| Theorem `thm:bounding` (per-divisor form) | `Pcf.Prop41Data.notMem_branch` |
| the containment `branch(g) ⊆ Σ` after Theorem `thm:bounding` | `Pcf.Prop41Data.branch_subset_bound`, `Pcf.Prop41Data.finite_bound`, `Pcf.Prop41Data.finite_branch` |

## D. Supporting formalizations

| Manuscript | Lean file | Status |
| --- | --- | --- |
| Strategy §`sec:intro` / Theorem `thm:bounding`, Step 3 (`O[z]/(z^e − ua, z) = O/(a)`) | `Pcf/LocalModel.lean` | proved |
| Example `ex:cusp`: `k[t]` is the integral closure of `k[t²,t³]` in their common fraction field, and `t ∉ k[t²,t³]` | `Pcf/Examples/Cusp.lean` (`isIntegralClosure_cuspAlg`, `isFractionRing_cuspAlg`, `X_not_mem_cuspAlg`) | proved |
| Example `ex:cusp`: the parametrization `k[x,y]/(y²−x³) → k[t]` and the Jacobian `2u` | `Pcf/Examples/Cusp.lean` (`cuspParam`, `jacobian_cuspSource`) | proved |
| Example `ex:cusp`: `B ∩ Z = {(0,0)}` | `Pcf/Examples/Cusp.lean` (`cusp_inter_branch`) | proved |
| Example `ex:branch-singular`: the quadric cone parametrization and the restriction `g(u) = u²` | `Pcf/Examples/Cusp.lean` (`coneParam`, `coneMap_restrict`) | proved |
| Example `ex:squaring` (squaring map on `P¹`), Example `ex:squaring-P2` (diagonal squaring) | `Pcf/Examples/Squaring.lean` | proved |
| Example `ex:wild` (wild counterexample, `deg_c(a_n) = (p+1)^{n−1}`) | `Pcf/Examples/CharP.lean` | proved |

## E. Not formalized at all

* Theorem `thm:general` (= `thm:A`) and hence Corollary `cor:pcfawd` *as stated for
  non-normal `X`*: the passage to the normalization needs `lem:normalization` in both
  directions, `lem:covers`, and the finiteness clause of `lem:lift`, none of which has a Lean
  counterpart. `Pcf.pcf_descent` is the descent for a chain of `PcfSetup`s, i.e. for normal
  stages with the bounding theorem assumed at each.
* `lem:restriction`, `eq:branch-normalization`, `lem:covers`, `prop:loci-compare`(3),
  `prop:pcf-equiv`(3), `lem:jacobian`, `ex:basilica`, `ex:dupont`, `ex:loci-compared`,
  `rem:why-normalized`, `q:sing-B`.
* In `ex:pinched`: everything scheme-theoretic (§B.8).
* In `ex:cusp`: the new sentence `branch₀(g) = branch₁(g) = {(0,0)} = B ∩ Z`.

* the integral-effective-divisor convention of §`sec:intro` (prime of a variety) and the definition of `Crit`/`Branch` as
  divisors on schemes.
* The **scheme-theoretic** halves of Steps 1 and 2 of the proof of Theorem `thm:bounding`:
  choosing the affine open `U`, verifying purity's hypotheses pointwise, and the
  étale-local descent that puts the cover in standard tame form. These are P1 and P2.
  The *reasoning* that joins them to the conclusion is now proved (§C).
* The regularity remark inside the proof of Theorem `thm:bounding`, and the
  strict-henselization / étale-base-change invariance of ramification indices. In the
  Lean development that invariance is folded into P2, which delivers the witness
  directly rather than delivering a pre-base-change extension.
* The identification of `Ideal.ramificationIdx` with the manuscript's `e(𝔮/𝔪)` from
  the ramification paragraph before Definition `def:crit-branch` for extensions of discrete valuation rings. Mathlib relates its two
  ramification-index definitions only under Dedekind hypotheses.
* A *scheme-theoretic* construction of a `Pcf.PcfGeometry`. The join
  (`Pcf.PcfGeometry.toPcfSetup`) exists, but nothing derives its data from an actual
  morphism of varieties — that bridge is assumption A1/A2.
* **Zariski–Nagata purity, any part of it.** It is assumed — faithfully, as
  `Pcf.Stacks.ZariskiNagataPurity` (§G.1), and in the older stronger form P1. What *is*
  machine-checked is the manuscript's own deduction of the global form **from** the local
  form (`Pcf.PurityData.codim_eq_one`), and now the manuscript's Step 1, which applies the
  local form (`Pcf.BoundingChart.isEtaleAt_of_notMem`).
* **Abhyankar's lemma itself** (Tags 0EYG/0EYH) is assumed as `Pcf.Stacks.AbhyankarLemma`
  (§G.1). Clauses 1 and 2 of Stacks Tag 0EYF are machine-checked standalone (§B.4). What is
  now **derived** from Abhyankar's lemma is Theorem `thm:bounding` (§G.3); the former
  disguised assumption P2 is removed.
* **One standard fact**: Tag 036W (étaleness is étale-local on the source), as the general
  ring-theoretic statement G4 of §G.2. Tags 033B and 01JT are proved (G3, G5).
* **Varieties.** The chart link A6 (§G.4) stands between the ring-level theorem and the
  abstract dynamics, for the same reason as A1–A5: no morphism of varieties is formalized.
* **The ramification index of the cover.** `Pcf.LocalModel.root_ne_zero_mod_algebraMap`
  establishes that the fibre of `R → R[z]/(z^e − ua)` over the divisor is non-reduced for
  `2 ≤ e`, which witnesses that the cover ramifies; but no statement computes the index and
  shows it equals `e`. `Ideal.ramificationIdx` is never applied to a cover in this
  development — only to maps that are already isomorphisms.
* The `Ω_{Ã/B̃}` coherence argument showing the non-étale locus is a *proper closed
  subset* (the input to P4); only the finiteness consequence is proved.
* The Proposition of §`sec:main` that the induced dynamical system `(Ã, g̃)` is finite,
  surjective and projective on a normal variety.
* Example `ex:cusp`'s conclusion `Branch(g) = ∅` *as a statement about a branch
  divisor*: the file proves the normalization facts that give it
  (`integralClosure_cuspAlg_eq_top` and `isIntegrallyClosed_polynomial`, so
  `B̃ = k[t] = A = Ã`), but there is no scheme-level `Branch(·)` in the model to
  state it against. Likewise `Crit(f) = V(u)` and `Branch(f) = V(x)` are not
  formalized: only the Jacobian `2u` is.
* Example `ex:branch-singular`'s assertions that `Y` is normal and singular only at the vertex,
  and that `f` is étale away from it.
* §`sec:intro`'s literature discussion, the remarks formerly numbered 4.3 and 4.6 (not in `paper.tex`),
  the paragraph after Example `ex:wild` (the tame case), and Examples `ex:dupont` and `ex:frobenius-line` beyond the
  concrete identities recorded in `Pcf/Examples/CharP.lean`.
* Dimension: Corollary `cor:pcfawd`'s "at most `dim X` steps" is not modelled;
  `Pcf.pcf_descent` proves the statement for a chain of any length.

## G. Theorem `thm:bounding` derived (2026-10-04): the inputs, side by side with the Stacks text

Human direction (Taylor Dupuy, 2026-10-04): "We need [the bounding theorem's conclusion] to
follow from the ZN purity and Abhyankar. ZN-regularity and Abhyankar are good to assume."
`lean/Pcf/Bounding/` does this. The conclusion of Theorem `thm:bounding` on an affine chart —
the restriction `R/(a) → S/𝔭` is étale at every prime of `S/𝔭` — is the theorem
`Pcf.BoundingChart.isEtaleAt_restriction`. Its inputs are the chart data (Step 0's standing
hypotheses), two classical theorems and three standard facts, every one of them stated as a
`Prop` about rings in `Pcf/Bounding/Stacks.lean` and *checked against the Stacks text fetched
on 2026-10-04*. Nothing valued in `KummerWitness` or `UnramifiedWitness` survives as a field.

### G.1 The two theorem-level inputs

| ID | Lean | Stacks | Verdict |
| --- | --- | --- | --- |
| G1 | `Pcf.Stacks.ZariskiNagataPurity R S`: for `Spec S → Spec R` with `R`, `S` Noetherian and `S` of finite type, at every prime `w` of `S` with `S_w` an integrally closed domain, `R_{w∩R}` regular local, `S` quasi-finite at `w`, `ht w = ht (w ∩ R) ≥ 1`, and `S` unramified over `R` at every `w' ≤ w` of height `1`: `S` is étale over `R` at `w`. | **0BMB**: `f : X → Y` locally Noetherian, `x ∈ X`, `y = f(x)`; (1) `𝒪_{X,x}` normal, (2) `𝒪_{Y,y}` regular, (3) `f` quasi-finite at `x`, (4) `dim 𝒪_{X,x} = dim 𝒪_{Y,y} ≥ 1`, (5) for `x' ⤳ x` with `dim 𝒪_{X,x'} = 1`, `f` unramified at `x'`. Then `f` étale at `x`. | **Faithful** (the affine special case). `x' ⤳ x` is `w' ≤ w` (`PrimeSpectrum.le_iff_specializes`); "normal" is integrally closed domain; `dim 𝒪_{X,x}` is `Ideal.height`; "quasi-finite at `x`" in Stacks presupposes finite type, so `Algebra.FiniteType R S` is a premise alongside `Algebra.QuasiFiniteAt`; `IsUnramifiedAt`/`IsEtaleAt` are the local-ring forms, which for finite-type algebras over Noetherian rings are the Stacks meaning. |
| G2 | `Pcf.Stacks.AbhyankarLemma R S a`: if `R` is Noetherian, `a` a nonzerodivisor, `R/(a)` regular, `S` finite over `R` and étale at every prime not containing `a`, `S` the integral closure of `R` in `S_a`, and every positive integer invertible in `R`, then for every prime `y ∋ a` there is an étale `R`-algebra `R'` with a prime over `y`, Noetherian, with `a` a nonzerodivisor in `R'`, `R'/(a)` regular with all local rings domains, and `R' ⊗_R S ≅ ∏ᵢ R'[zᵢ]/(zᵢ^{eᵢ} − uᵢ a)` as `R'`-algebras, `eᵢ ≥ 1` invertible in `R'`. | **0EYG**: `X` locally Noetherian, `D ⊂ X` effective Cartier and regular, `Y → X ∖ D` finite étale and tamely ramified over `X` in codim 1 ⟹ étale locally on `X`, `Y → X` is a finite disjoint union of standard tamely ramified morphisms. **0EYH**: the normalization `Y'` of `X` in `Y` is finite locally free and étale locally on `X` a finite disjoint union of `Spec(A[x]/(x^e − f)) → Spec(A)`, `A` Noetherian, `f` a nonzerodivisor, `A/fA` regular, `e ≥ 1` invertible in `A`. | **Weaker** than 0EYG + 0EYH, modulo one lemma Mathlib lacks. Weaker because: (i) the premise "tamely ramified in codimension 1" is replaced by the stronger "every positive integer is invertible" (characteristic zero, the manuscript's standing hypothesis); (ii) the conclusion allows units `uᵢ` (the manuscript's form; 0EYH has `uᵢ = 1`); (iii) only points of `D` are covered; (iv) "finite étale over `X ∖ D`" is written pointwise, which for a finite algebra over a Noetherian ring is equivalent. Adjoined: "every local ring of `R'/aR'` is a domain", a consequence of "`R'/aR'` regular" by **00NP** (a regular local ring is a domain), which Mathlib does not have; with 00NP the Lean conclusion is equivalent to 0EYH's. |

**Could either be equivalent to the conclusion?** No, and for a reason visible in the types:
neither Prop mentions `𝔭`, the quotient `S/𝔭`, or the map `R/(a) → S/𝔭`. Both are statements
about the cover `R → S` alone. The conclusion is about a different ring map. Moreover both
are *true theorems* (special cases of the cited tags), so assuming them assumes nothing false,
and `Pcf.Stacks.ZariskiNagataPurity.of_etale` shows purity is satisfied by any étale cover
with no information about any divisor. The self-check required by the task — try to prove the
conclusion from each input alone — fails structurally: from G1 alone one reaches Step 1
(`Pcf.BoundingChart.isEtaleAt_of_notMem`, étaleness of `S` over `R` off `a`) and nothing about
`S/𝔭`; from G2 alone one cannot even discharge G2's premise "étale off `a`", which only G1
supplies, and G2's conclusion is a decomposition of `R' ⊗_R S`, which reaches the restriction
only through Step 3 (`Pcf.LocalModel.quotientMap_bijective`, `radical_span_algebraMap_eq_span_root`)
and Step 4 (`Pcf/Bounding/LocalStructure.lean`), both proved.

### G.2 The three standard facts, isolated as hypotheses

| ID | Lean | Stacks | Verdict |
| --- | --- | --- | --- |
| G3 | `Pcf.Stacks.isReduced_of_etale_of_isDomain`: an étale algebra over a **domain** is reduced. | **033B**: `φ : R → S` smooth, `R` reduced ⟹ `S` reduced. | **PROVED** (`Pcf/Bounding/Reduced.lean`), for the case used: the étale algebra is flat, so it injects into its base change to the fraction field, which is étale over a field and hence reduced (Mathlib `Algebra.FormallyUnramified.isReduced_of_field`). Used once: the base change `S/𝔭 → (R' ⊗_R S)/𝔭` of the integral `A ∩ V` is reduced, Step 3's "`T` is reduced because `V' → V` is étale". |
| G4 | `Pcf.Stacks.EtaleLocalOnSource`: for all `A → B → B'` with `B → B'` étale, if `A → B'` is étale at every prime and `ξ ∈ Spec B` is under some prime of `B'`, then `A → B` is étale at `ξ`. | **036W**: "`f` is étale" is étale local on the source; with **03WT** (étale morphisms are open) for the passage from a covering of the open image to the point. | **ASSUMED; weaker** (a pointwise consequence). Used once, in Step 4's last sentence. The only standard fact still assumed. Mathlib has descent of étaleness along *faithfully flat* base change (`Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat`), from which this could be derived by localizing at `ξ` (flat local maps are faithfully flat); not attempted. |
| G5 | `Pcf.Stacks.ExistsPrimeOverBoth`: for all `R → S`, `R → T`, primes `p ⊂ S`, `q ⊂ T` over the same prime of `R` lie under a common prime of `T ⊗_R S`. | **01JT**: points of `X ×_S Y` ↔ quadruples `(x, y, s, 𝔭)` with `𝔭` a prime of `κ(x) ⊗_{κ(s)} κ(y)`, a nonzero ring. | **PROVED** (`Pcf.Stacks.existsPrimeOverBoth`, `Pcf/Bounding/FibreProduct.lean`) from Mathlib's `AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback` and `pullbackSpecIso`. Used once: "choose a point `ξ'` of `T` over `ξ`". |

G4 is universally quantified over the rings of a universe; it cannot be specialized to the
chart, so it cannot encode the conclusion. It is what the manuscript cites in passing
(Tag 036W), and it is isolated because Mathlib does not have it.

### G.3 What is proved in `Pcf/Bounding/`

| Manuscript | Lean | Status |
| --- | --- | --- |
| Step 1 | `Pcf.BoundingChart.isEtaleAt_of_notMem` | proved from G1 and the chart's standing hypotheses, including the generic-point case from `generic_etale` |
| Step 2 | `Pcf.BoundingChart.exists_standardPieces` | G2 applied; its seven premises discharged by the chart and Step 1 |
| `eq:standard-piece`: `(C/aC)_red = C/zC` | `Pcf.LocalModel.radical_span_algebraMap_eq_span_root` | proved: `√(aC) = (z)` when `R/(a)` is reduced |
| Step 3, `V(z) → V(a)` an isomorphism | `Pcf.LocalModel.quotientMap_bijective` | proved (the canonical map; this is `restrictionMap_bijective`) |
| Step 3, the dimension count | `Pcf.Bounding.mem_minimalPrimes_span_of_mem_minimalPrimes_map` | proved without dimensions: a minimal prime over `𝔭C` is minimal over `aC`, by going down for flat maps (Mathlib `Algebra.HasGoingDown.of_flat`) and incomparability in quasi-finite fibres (Mathlib `Algebra.QuasiFiniteAt.eq_of_le_of_under_eq`) |
| Step 3, "union of connected components" | `Pcf.Bounding.exists_mul_mem_ker_of_mem_minimalPrimes_ker` | proved at a point: a minimal prime over `(z)` vanishes locally where the local ring of `R'/(a)` is a domain |
| Step 4, `T → D'` étale at `ξ'` | `Pcf.Bounding.isLocalization_of_localStructure`, `formallyEtale_of_localStructure`, `Pcf.BoundingChart.isEtaleAt_quot_of_pieces` | proved: the local ring of the base-changed restriction is a localization of `R'/(a)` |
| the piece through a point | `Pcf.Bounding.exists_isUnit_evalRingHom_single`, `exists_lift_of_isUnit_single`, `isLocalizationAway_evalRingHom` | proved |
| Step 4, descent to `g` | `Pcf.BoundingChart.isEtaleAt_restriction` | proved from the above plus G4 (assumed) and G5 (proved); G3 (proved) is used inside |
| the étale conclusion for the dynamics | `Pcf.PcfSetupChart.key1`, `toPcfSetup1`, `res_pcf1`, `res_pcf`, `res_pcf1_of_iter` | proved from the chart link A6 |

Tameness of the `eᵢ` is consumed only inside G2; Steps 3–4 hold for any `e ≥ 1`
(`Pcf.BoundingChart.isEtaleAt_quot_of_pieces` takes `e i ≠ 0` only).

### G.4 The chart link A6, and exactly what it is worth

`Pcf.PcfSetupChart` is `Pcf.PcfSetup1` with `key1` replaced by `chart`: for each `m ≥ 1`,
good `Q`, and `Q'` over `Q`, a `Pcf.BoundingChart` and a point `ξ` representing `Q'`, with
`Q' ∈ crit₁(gᵐ) → ¬ IsEtaleAt (R/(a)) ξ`. `Pcf.PcfSetupChart.key1` then derives `key1`.

**Honesty check.** The abstract carrier `PA` has no rings attached (A1–A5). So the link is
necessarily supplied by whoever supplies the data, and it is exactly as strong as `key1`
*relative to the derived theorem*: given `key1`, `chart` could be discharged for every `Q'`
with a trivial chart (the identity cover `ℚ[x] → ℚ[x]`, `a = x`, satisfies every field of
`Pcf.BoundingChart`); given `chart`, `key1` follows. This is **not** the situation the reviews
of §B.2 refuted: there, the supplier chose the algebra to which Abhyankar's lemma was applied,
and no geometry crossed. Here the algebra is the chart's own `R → S`, G1 and G2 are applied
to *it*, and the only thing left to the supplier is to say which chart represents which
abstract prime. What has changed is where the mathematics lives — Steps 1–4 are theorems — and
not the trust boundary of the abstraction, which cannot move without formalizing varieties.
The report to the human says this in the same words.

### G.5 Removed

`Prop41Data.over`, `Prop41Data.ram`, `Prop41Data.standardForm`, `Prop41Data.branch`,
`Prop41Data.notMem_branch`, `Prop41Data.branch_subset_bound`, `Prop41Data.finite_branch`,
`PcfGeometry.standardForm`, `PcfGeometry.key` (the theorem); `PcfGeometry.toPcfSetup`,
`res_pcf`, `res_pcf_of_iter` and `PcfGeometry.ofPurityData` / `res_pcf_of_purityData` now take
the bounding conclusion as an explicit argument. The cofinite witness
(`Pcf/Examples/CofiniteWitness.lean`) supplies it directly (`Pcf.Examples.resDyn_key`), with
no `KummerWitness`.

## F. Status of the formalization

* `Pcf/Unnormalized.lean` — **LEAN-PROVED** given U1–U6; Theorem `thm:normal-invariant` in
  its `1`-PCF form via `Pcf.PcfSetup1.res_pcf1` is **CONDITIONAL** on A1–A5, B1–B4 and U1–U6.
* `Pcf/Examples/Pinched.lean` — ring-level statements **LEAN-PROVED**; the dynamical
  statements are **CONDITIONAL** on `o ∈ crit₀(g)` (a hypothesis or a stipulated field).

Using the vocabulary of the formalization-evidence contract:

* `Pcf/Dynamics.lean`, `Pcf/Restriction.lean`, `Pcf/LocalModel.lean`,
  `Pcf/Examples/*` — **LEAN-PROVED**: they compile, and `#print axioms`
  reports only standard logical axioms.
* Theorem `thm:normal-invariant` via `Pcf.PcfSetup.res_pcf` — **CONDITIONAL** on A1–A5 and B1–B5,
  because those are fields of the structure it takes as input.
* Theorem `thm:normal-invariant` via `Pcf.PcfGeometry.res_pcf` — **CONDITIONAL** on A1–A5, B1, B2 and
  P1–P6. B3 and B4 are genuinely discharged; B5 is *restated* as P2, not discharged.
* Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many` and (3) — the finiteness half is **proved**; the properness half
  is assumed (P5, P6).
* Theorem `thm:bounding` on an affine chart — **LEAN-PROVED, CONDITIONAL** on the chart's
  standing hypotheses, G1 (Zariski–Nagata purity, Tag 0BMB), G2 (Abhyankar's lemma, Tags
  0EYG/0EYH) and the standard fact G4 (Tag 036W): `Pcf.BoundingChart.isEtaleAt_restriction`
  (§G). Tags 033B and 01JT are proved along the way.
* Theorem `thm:normal-invariant` via `Pcf.PcfSetupChart.res_pcf1` — **CONDITIONAL** on
  A1–A6, B1–B4, U1–U5, G1, G2, G4. The former P2/U6 primitive is derived.
* The global form of Zariski–Nagata purity, given the local form — **PROVED**
  (`Pcf.PurityData.codim_eq_one`).

This is not a machine verification of "PCF All the Way Down". It is a machine-checked
derivation of Theorem `thm:normal-invariant`, Corollary `cor:normal-preperiodic` and
Corollary `cor:pcfawd` from Theorem `thm:bounding` and the divisorial bookkeeping; a
machine-checked derivation of Theorem `thm:bounding` on an affine chart from Zariski–Nagata
purity and Abhyankar's lemma, stated as the Stacks Project states them, plus three cited
standard facts; a machine-checked derivation of the global form of purity from the local
form; machine-checked finiteness statements; machine-checked proofs of the supporting
examples; and constructors joining the geometric data to the structure Theorem
`thm:normal-invariant` consumes.

Purity and Abhyankar's lemma themselves are **assumed**. Two gaps remain at the bottom: no
Lean code derives a `Pcf.PcfSetup` or a `Pcf.BoundingChart` from an actual morphism of
varieties (assumptions A1–A6), and no part of purity or of Abhyankar's lemma is
machine-checked beyond clauses 1–2 of Tag 0EYF.
