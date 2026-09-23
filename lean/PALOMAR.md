# Palomar registry entries — `tdupu/pcf`

Prepared for submission to the [Palomar registry](https://palomar-registry.org/),
which records a claim about **one exact version** of a repository: the formal
statement, dependencies, toolchain, and verification result. Palomar separates the
statement from the solution, checks the proof with Lean's kernel and an independent
kernel implementation, and runs language-model review for **mismatch between the
informal claim and the formal statement**.

That last check is the one this submission is built around. Every informal claim below
is a rendering of the **elaborated type as printed by Lean**, not of my memory of it,
and every entry carries an explicit *does not claim* block. An earlier phase of this
development produced three claims that overstated what the corresponding formal
statements delivered; all three were retracted, and the retractions are themselves
registered here as entries 9–11.

## Pin

| Field | Value |
| --- | --- |
| Repository | `github.com/tdupu/pcf` |
| Commit | *the commit introducing this file* — supply at submission time |
| `lean/` subtree | `f7bf72d05a6839ba1290ec08561736d603512fe1` at the time of writing; recompute with `git rev-parse HEAD:lean` (stable across manuscript-only commits, but this file now lives inside `lean/`, so it moves when this file changes) |
| Toolchain | `leanprover/lean4:v4.34.0` |
| Mathlib | `leanprover-community/mathlib4`, rev `5ed2965256430c3649e86755f9576b54eca72435` (`inputRev` `v4.34.0`) |
| Build | `lake build` — 2584 jobs, 0 errors, 0 warnings |
| Audit | `lean/Pcf/Audit.lean`, 160 declarations, all on `propext`, `Classical.choice`, `Quot.sound` |
| Forbidden tokens | no `sorry`, `axiom`, `admit`, `native_decide` in `lean/Pcf/` |

The Mathlib revision was confirmed two ways — the `rev` field of `lake-manifest.json`
and `git rev-parse HEAD` in `.lake/packages/mathlib` — because a first attempt to read
it by `grep` returned the repository's own HEAD instead, which would have frozen a
wrong pin into a permanent record.

Accompanying manuscript: `latex/pcf.tex`. Assumption census: `AXIOMS.md`, beside this
file. Statement-to-declaration map: `README.md`, likewise.

**Status: prepared, not submitted.** No submission to the Palomar registry has been
made. This file is the manifest of what a submission would assert; submitting is a
separate, explicitly authorized act.

> **Correction (2026-09-23).** An earlier version of this file, and of the commit
> message introducing it, said there is "no submission tooling in this environment" and
> that Palomar is "wired in only as a search channel". **That is false.** Palomar
> publishes an agent-facing submission protocol at
> `https://submit.palomar-registry.org/llms.txt`: `POST /api/submit`, a verification
> tag and secret gist, `POST /api/verify`, `GET /api/review`, `POST /register`, and
> `POST /withdraw`. The step is reachable. What prevents submission is the instruction
> not to make one — not the absence of a path — and that distinction matters, because
> the first is a decision and the second would have been a safeguard.
>
> The protocol's own gates are stricter than anything this file previously stated, and
> they govern: **do not drive the browser sign-in** in any form; before verifying,
> confirm with the user the repository, the commit, the Comparator configuration path,
> and the answer to be given for their relationship to the formalization, since that is
> a permanently recorded claim *about them*; treat the access token as a credential; and
> **register only after showing the user the private review and being told to**.
>
> This file is also **not yet a submission package**. A registered record requires a
> challenge/solution split, a Comparator configuration, a `formalization.yaml`, and the
> `schema-v3.json` fields — `title`, `abstract`, `authors`, `classification`, `source`
> with a `license`, `provenance`, `theorem_names`, `permitted_axioms` — none of which
> appear below. `permitted_axioms` is a closed set of exactly `propext`, `Quot.sound`
> and `Classical.choice`, which the entries here do satisfy. What follows is a claim
> manifest, useful as the informal-vs-formal half of a submission and not a substitute
> for it.

---

# Entry 1 — the descent (CONDITIONAL)

**Declaration** `Pcf.pcf_all_the_way_down`

```
∀ {P : ℕ → Type u_1} (D : (i : ℕ) → Pcf.DivDyn (P i))
  (S : (i : ℕ) → Pcf.PcfSetup (P i) (P (i + 1))),
  (∀ (i : ℕ), (S i).res = D (i + 1)) →
    (∀ (i : ℕ), ∃ n, 1 ≤ n ∧ (S i).amb = (D i).iter n) →
      (D 0).PCF → ∀ (i : ℕ), (D i).PCF
```

**Informal claim.** In the abstract model of divisorial dynamics defined in this
repository, consider a tower in which each stage `i` supplies a system `D i` together
with data `S i` exhibiting a prime that is periodic with some return time `n ≥ 1`, and
whose induced system is the next stage. If stage `0` is post-critically finite, then
**every** stage is. The proof is an induction on `i`.

This is the second paragraph — the descent — of the conjecture the project is named
after: Conjecture 2.6 of `latex/pcf.tex`, due to the authors and quoted on page 2 of
A. Bridy, P. Ingram, R. Jones, J. Juul, A. Levy, M. Manes, S. Rubinstein-Salzedo and
J. H. Silverman, *Finite ramification for preimage fields of post-critically finite
morphisms*, Math. Res. Lett. **24** (2017), no. 6, 1633–1647; `arXiv:1511.00194`.

**Does not claim.**

* **This is not a statement about varieties.** `Pcf.DivDyn` and `Pcf.PcfSetup` are
  abstract structures. Nothing in this repository constructs a `Pcf.DivDyn` from a
  morphism of schemes; that bridge is assumptions A1–A5 of `lean/AXIOMS.md`.
* **Proposition 4.1(2) of the manuscript is assumed**, as the field `PcfSetup.key`.
  It is not proved here, and three attempts to reduce it were retracted — see
  entries 9–11.
* **Lying over is assumed** (`DivDyn.step_surjective`), and so is finiteness of the
  branch divisor for the ambient system (`DivDyn.branch_finite'`).
* **The tower is given, not produced.** The statement asserts nothing about the
  existence of periodic primes at any stage.
* **The recursion does not terminate.** The manuscript's "at most `dim X` steps" is
  not modelled; the abstraction carries no dimension.

**Axioms.** `[propext, Classical.choice, Quot.sound]`

---

# Entries 2–4 — Stacks Tag 0EYF, clauses 1–2

**Declaration** `Abhyankar.etale`

```
∀ {R : Type u_1} [inst : CommRing R] (u : Rˣ) {e : ℕ},
  e ≠ 0 → IsUnit ↑e → Algebra.Etale R (AdjoinRoot (Abhyankar.kummerPoly u e))
```

**Informal claim.** Let `R` be a commutative ring, `u` a unit of `R`, and `e ≥ 1` an
integer whose image in `R` is a unit. Then the Kummer algebra `R[y]/(yᵉ − u)` is étale
over `R`.

Both hypotheses are necessary, and two companion entries prove it rather than
asserting it:

**Declaration** `Abhyankar.not_etale_wild`

```
∀ {k : Type u_1} [inst : Field k],
  (2 : k) = 0 → ¬Algebra.Etale k (AdjoinRoot (Abhyankar.kummerPoly (1 : kˣ) 2))
```

**Informal claim.** Over any field of characteristic `2`, the algebra `k[y]/(y² − 1)`
is **not** étale — so the conclusion above genuinely fails without tameness, not
merely its proof.

**Declaration** `Abhyankar.not_etale_of_not_isUnit`

```
∀ {k : Type u_1} [inst : Field k] (u : kˣ) {e : ℕ},
  2 ≤ e → ¬Algebra.Etale k (AdjoinRoot (Abhyankar.ramifiedPoly u 0 e))
```

**Informal claim.** For `e ≥ 2`, the algebra `k[y]/(yᵉ)` — the ramified model with
constant term `0` — is not étale over `k`.

**Does not claim.**

* **This is not Stacks Tag 0EYF.** That tag makes three assertions about
  `C = A[x]/(xᵉ − f)`. Clause 1 (finite locally free) is proved separately as
  `Abhyankar.finrank`, with freeness and finiteness supplied by Mathlib's
  `Polynomial.Monic.free_adjoinRoot` and `Monic.finite_adjoinRoot`. Clause 2 is the
  entry above. **Clause 3 — tame ramification in codimension one — is not proved and
  is not stated anywhere in this repository.** It is the clause the name "standard
  *tamely ramified* morphism" refers to, and the clause the proof of Tag 0EYG
  consumes.
* **This is not Abhyankar's lemma.** Tag 0EYG, the structure theorem, is not proved.
* **The separability input is Mathlib's**, not this repository's:
  `Polynomial.separable_X_pow_sub_C_unit`.

**Axioms.** All three: `[propext, Classical.choice, Quot.sound]`

---

# Entry 5 — separable monic implies standard étale

**Declaration** `Abhyankar.isStandardEtale_adjoinRoot_of_separable`

```
∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R},
  f.Monic → f.Separable → Algebra.IsStandardEtale R (AdjoinRoot f)
```

**Informal claim.** If `f` is a monic separable polynomial over a commutative ring `R`,
then `R[X]/(f)` is a standard étale `R`-algebra.

**Context.** `Polynomial.Separable` (`= IsCoprime f (derivative f)`) and
`Algebra.IsStandardEtale` both exist in Mathlib; a search of
`Mathlib/RingTheory/{Etale,Unramified,Smooth}`, `Mathlib/FieldTheory/{Separable,
KummerExtension}`, `Mathlib/RingTheory/AdjoinRoot`, and of the Tau Ceti tree found no
lemma connecting them. That is the evidence available and is **not** a claim of
novelty.

**Does not claim.** No claim that this is absent from the literature, or that any
library would accept it.

**Axioms.** `[propext, Classical.choice, Quot.sound]`

---

# Entry 6 — local purity implies global purity

**Declaration** `Pcf.PurityData.codim_eq_one`

```
∀ {X : Type u_1} [inst : TopologicalSpace X] {D : Pcf.PurityData X} [T0Space X]
  {E₀ : Set X}, D.IsComponent E₀ → ∀ {η : X}, closure {η} = E₀ → D.codim η = 1
```

**Informal claim.** Let `X` be a `T0` topological space carrying a `Pcf.PurityData` —
a structure whose fields supply a codimension function, a closed proper "non-étale"
subset, and, as the field `localPurity`, **the local form of the Zariski–Nagata purity
theorem**. Then every irreducible component of that subset has a codimension-one
generic point: the global form of purity.

This is the one passage of §4 of the manuscript that the authors reasoned out rather
than quoted, because the cited SGA reference recalls the theorem without proof.

**Does not claim.**

* **Purity is not proved.** `localPurity` is a *field* of the input structure. This
  entry records an implication, local form ⟹ global form, and nothing more.
* **The assumed field is stronger than Stacks Tag 0BMB**, which it is meant to render:
  0BMB carries four hypotheses (`𝒪_{X,x}` normal, `𝒪_{Y,y}` regular, `f` quasi-finite
  at `x`, and a dimension equality) that `localPurity` omits, so the field applies
  where the tag does not. `lean/AXIOMS.md` entry P1 records this.

**Axioms.** `[propext, Classical.choice, Quot.sound]`

---

# Entry 7 — ramified implies non-étale

**Declaration** `Pcf.mem_nonEtaleLocus_of_one_lt_ramificationIdx`

```
∀ (R : Type u_1) (S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S]
  [inst_2 : Algebra R S] [Algebra.EssFiniteType R S] (q : PrimeSpectrum S),
  1 < q.asIdeal.ramificationIdx R → q ∈ Pcf.nonEtaleLocus R S
```

**Informal claim.** For an essentially-finite-type algebra `S` over `R`, a prime of
`Spec S` whose ramification index over `R` — in Mathlib's sense,
`Ideal.ramificationIdx` — exceeds `1` lies in the non-étale locus of `R → S`.

**Does not claim.** The identification of `Ideal.ramificationIdx` with Definition 2.2
of the manuscript (the exponent in `𝔪R = 𝔮₁^{e₁}···𝔮ₙ^{eₙ}` for the discrete valuation
ring of a divisor prime) **is not formalized**; `lean/AXIOMS.md` §E records this.

**Axioms.** `[propext, Classical.choice, Quot.sound]`

---

# Entry 8 — lying over

**Declaration** `Pcf.comap_surjective_of_isIntegral_of_injective`

```
∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S]
  {φ : R →+* S}, φ.IsIntegral → Function.Injective ⇑φ →
    Function.Surjective (PrimeSpectrum.comap φ)
```

**Informal claim.** Lying over (Stacks Tag 00HS): if `φ : R → S` is an injective
integral ring homomorphism, the induced map `Spec S → Spec R` is surjective.

**Does not claim.** This does **not** discharge `Pcf.DivDyn.step_surjective`, which is
about a self-map of *divisors* rather than points. Transporting it there would require
that the image of a closed set under a finite morphism is closed and that codimension
is preserved; neither is available here.

**Axioms.** `[propext, Classical.choice, Quot.sound]`

---

# Entries 9–11 — machine-checked retractions

These are negative results, and they are registered deliberately. Each records that an
interface used in this development is equivalent to its own conclusion, or
interderivable with one it was claimed to improve on — that is, that a claimed
reduction of assumptions reduces nothing. Each was produced by adversarial review after
the corresponding positive claim had already been written into the repository's
documentation, and in one case into the manuscript.

They are stated in Lean precisely so that the development contradicts its own
overclaims in machine-checked form rather than in prose a reader must trust.

**Declaration** `Pcf.nonempty_unramifiedWitness_iff`

```
∀ (n : ℕ), Nonempty (Pcf.UnramifiedWitness n) ↔ n = 1
```

**Informal claim.** The witness interface `Pcf.UnramifiedWitness n` is inhabited
exactly when `n = 1`. Since `n = 1` is the conclusion the interface was introduced to
deliver, supplying such a witness is supplying the conclusion.

**Declaration** `Pcf.kummerWitness_iff_unramifiedWitness`

```
∀ (n : ℕ), Nonempty (Pcf.KummerWitness n) ↔ Nonempty (Pcf.UnramifiedWitness n)
```

**Informal claim.** The replacement interface `Pcf.KummerWitness` and the interface it
replaced are interderivable, uniformly in `n`, with no hypotheses. The replacement
therefore restated the assumption rather than weakening it.

**Declaration** `Pcf.PurityData.ofZariskiNagata_toZariskiNagata`

```
∀ {X : Type u_1} [inst : TopologicalSpace X] (D : Pcf.PurityData X),
  Pcf.PurityData.ofZariskiNagata D.toZariskiNagata ⋯ ⋯ ⋯ ⋯ ⋯ ⋯ ⋯ = D
```

**Informal claim.** A `Pcf.PurityData` can be converted to a `Pcf.ZariskiNagata` — a
structure stating Stacks Tag 0BMB with all five of its hypotheses present — and back,
and the roundtrip is the identity, definitionally. The two are therefore
interderivable, and restating the tag with its hypotheses did not make the assumption
more faithful.

**Axioms.** All three: `[propext, Classical.choice, Quot.sound]`

---

## Reviewer notes

* `lean/AXIOMS.md` is the assumption census and is the document to read before drawing
  conclusions from any `#print axioms` output. Reporting only the three standard axioms
  is **not** a claim that nothing is assumed: the assumed mathematics is carried in
  *fields* of `Pcf.DivDyn`, `Pcf.PcfSetup` and `Pcf.PurityData`, and structure fields
  are invisible to `#print axioms` by construction.
* Two adversarial reviews are retained at
  `ai/2026-09-21-abhyankar-formalization/adversarial-review.md` and
  `ai/2026-09-21-zariski-nagata/adversarial-review.md`.
* **Correction to this file's introducing commit.** The commit message of `facc8e2`
  states "Mathlib is for human-only formalizations" (that commit created this file at
  `palomar/registry-entries.md`, before it was moved here). That is **false as stated**, and
  is corrected here because a commit message cannot be amended after pushing.
  `leanprover-community.github.io/contribute/` does **not** categorically exclude
  AI-authored contributions: it permits them subject to disclosure of which tools were
  used and how, an `LLM-generated` label for substantial LLM-written code, the
  requirement that a human understand all AI-written content and be able to justify
  each decision to reviewers *without* AI assistance, a prohibition on LLM-written
  GitHub and Zulip comments, and a quality bar the page states that unsupervised
  AI-written code currently fails "by a large margin". The binding constraint is a
  human who has done the understanding and will stand behind it publicly — not machine
  authorship.

  The routing conclusion is unaffected: this work goes to Palomar for provenance and
  then to Tau Ceti, and no agent-authored Mathlib pull request is contemplated. But the
  reason is that an autonomous pipeline cannot meet Mathlib's human-understanding
  requirement, not that AI authorship is banned. Do not cite this repository for
  "Mathlib bans AI".

* No author has reviewed the formalization. Compilation certifies the formal
  statements; it does not certify that they render the statements of `latex/pcf.tex`,
  and that comparison has not been completed.
