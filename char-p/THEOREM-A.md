# Theorem A: characteristic zero, characteristic p, all codimensions

Source: the characteristic-`p` manuscript *PCF all the way down*
(`paper-p.tex`, not yet public), Theorem `thm:A`, Definition
`def:pcfawd-allsubvar`, and the normalized blow-up argument
`thm:allcodim-normal`. Labels below are that manuscript's `\label`s.

## Statements

Theorem A, in the paper's form (postcritical divisors counted on `X`):

- `Pcf.isPCFAllSubvarieties_charZero_of_downstairsPCF`: characteristic zero.
- `Pcf.isPCFAllSubvarieties_charP_of_downstairsPCF`: characteristic `p > 0`,
  with prime-to-`p` monodromy (`Pcf.IsPrimeToPMonodromyMap`, `def:prime-to-p`).

The PCF hypothesis `Pcf.IsWeightedNormalizedPCFDownstairs` is `def:pcf` with
the normalized weighted critical locus of `def:crit-branch`
(`δ = e · [κ : κ]_insep > 1` on the normalization `X^ν`), counted by its
images on `X`. `Pcf.isWeightedNormalizedPCFDownstairs_iff` shows that this is
finiteness of the weighted postcritical set on `X^ν`; the reverse implication
uses the finite fibres of the normalization map.

The conclusion `Pcf.IsPCFAllSubvarieties` (`def:pcfawd-allsubvar`) quantifies
over every recursion depth, every proper integral closed subvariety (any
codimension, closed points included), every preperiod `r ≥ 0` and every
period `s ≥ 1` with `f^{r+s}(C) = f^r(C)`. Each return is the actual morphism
`f^s` on the original reduced closure of `f^r(C)`. At every node the PCF
predicate is `Pcf.IsSeparableNormalizedPCF`, stated with the non-étale
divisor locus of the normalization lift;
`Pcf.isSeparableNormalizedPCF_iff_downstairs` identifies it with generic
separability plus `IsWeightedNormalizedPCFDownstairs`, that is, with `def:pcf`.

Equivalent forms with the PCF hypothesis on the normalization lift:

| Form of the PCF hypothesis | Characteristic zero | Characteristic `p` |
| --- | --- | --- |
| non-étale locus on `X^ν` (`IsSeparableNormalizedPCF`) | `Pcf.isPCFAllSubvarieties_charZero` | `Pcf.isPCFAllSubvarieties_charP` |
| weighted `δ` locus on `X^ν` | `Pcf.isPCFAllSubvarieties_charZero_of_weightedPCF` | `Pcf.isPCFAllSubvarieties_charP_of_weightedPCF` |

The bridge between the two rows is
`Pcf.isSeparableNormalizedPCF_iff_weightedNormalLift`.

## PCF all the way down on divisors

`Pcf.IsPCFAllDivisors` is the divisorial recursion `def:pcfawd`: the same
PCF predicate and returns, quantified over codimension-one points only.
`Pcf.IsPCFAllSubvarieties.isPCFAllDivisors` derives it from the
all-subvariety property, giving
`Pcf.isPCFAllDivisors_charZero_of_downstairsPCF` (`cor:pcfawd`) and
`Pcf.isPCFAllDivisors_charP_of_downstairsPCF` (`cor:charp-pcfawd`).

## Scope relative to the paper

- The paper's variety is an integral separated scheme of finite type over `k`.
  The Lean assumes an integral scheme locally of finite type over `k` with
  Noetherian underlying space; it does not assume separatedness, and it does
  not require `f` to be a morphism over `k`.
- "Finite surjective" is `IsFinite` and `IsDominant`; for a finite map these
  are equivalent.
- In characteristic zero there is no monodromy hypothesis.

## Proof outline

The proof derives generic fibre multiplicity one in characteristic zero and
a prime-power multiplicity in characteristic `p` (`lem:primary-fibres`),
bounds the bad codimension-one points of the centre, and applies a tame chart
to the finite map of normalized Rees blow-ups. The valuation comparison makes
the normalized return étale outside a fixed finite set (`thm:allcodim-normal`).
The finite-cover induction and the PCF transfer (`lem:pcf-transfer-charp`)
then give the recursive statement (`thm:allsubvar-pcfawd`).

## Verification

`lake build` in this directory builds every module. `#print axioms` on each
theorem named above prints only `propext`, `Classical.choice` and
`Quot.sound`; the `#print axioms` lines are at the ends of
`Pcf/Bounding/TheoremACharP.lean`, `TheoremACharPWeighted.lean`,
`TheoremACharZero.lean`, `TheoremAWeightedDownstairs.lean` and
`TheoremADivisors.lean`. The three
`sorry` declarations in `PcfChallenge.lean` (now `legacy/entry-0/PcfChallenge.lean`) are the Palomar Challenge
statements and are not dependencies of these theorems.
