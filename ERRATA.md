# Errata

Errors found in the plan and in the sources it cites while formalizing them,
and what the library does about each. `AGENTS.md` says when to add an entry.

There is a section for each page of the plan, in the plan's order, headed
with the page's file name, such as `## atlas/linear-symplectic-geometry.md`,
and `## Other sources` last, for errors in sources that no page covers. Add a
missing section in its place in that order. Within a section, entries go in
alphabetical order of their titles, with a blank line between them, so that
two pull requests conflict only when their entries land in the same place.

Each entry has this form:

```markdown
### <A short title>

- **Where:** the plan's page and milestone, or the source and its location.
- **Error:** what it says, in your own words for the atlas, which is
  private and must not be quoted, or quoted for a published source; and why
  that is wrong: a counterexample, or the step that is false or does not
  follow.
- **Fix:** what the library proves instead, or the route it takes, naming the
  declarations.
  Or, while there is none, **Unresolved:** the routes tried, and where each
  failed.
- **Issue:** #<number>.
```

## atlas/linear-symplectic-geometry.md

### Complex structures on the zero space form one component

- **Where:** `atlas/linear-symplectic-geometry.md`, *Linear complex
  structures are standard*.
- **Error:** the milestone says, with no bound on $n$, that the space of
  linear complex structures on $\mathbb{R}^{2n}$ has two connected
  components. For $n=0$ this is false: the zero space carries exactly one
  complex structure, the zero map (its square is $0=-\mathbb{1}$), so the
  space is a single point and has one component. The quotient
  $\mathrm{GL}(0,\mathbb{R})/\mathrm{GL}(0,\mathbb{C})$ is a point too.
- **Fix:** `nat_card_connectedComponents_almostComplexStructure_stdSpace`
  counts two components for `Nonempty ι`, the generality in which the book's
  argument works, and the milestone `complexStructures_classification` has
  the hypothesis `n ≠ 0` in its third conjunct. The counterexample is
  `nat_card_connectedComponents_almostComplexStructure_stdSpace_of_isEmpty`:
  for empty `ι` the count is one. The other conclusions of the milestone are
  stated for every $n$ (`design/linear-complex-structures.md`).
- **Issue:** #16.

### The fundamental group of U(n) in dimension zero

- **Where:** `atlas/linear-symplectic-geometry.md`, *Fundamental group of the
  unitary group*.
- **Error:** the milestone asserts, with no bound on $n$, that the complex
  determinant induces an isomorphism from $\pi_1(\mathrm{U}(n))$ onto
  $\pi_1(S^1)\cong\mathbb{Z}$, and that $\pi_1(\mathrm{Sp}(2n))\cong\mathbb{Z}$.
  For $n=0$ this is false: `Matrix.unitaryGroup (Fin 0) ℂ` and
  `Matrix.symplecticGroup (Fin 0) ℝ` each have one element (the empty matrix),
  so their fundamental groups are trivial, while $\pi_1(S^1)\cong\mathbb{Z}$.
- **Fix:** the *Unitary group topology* part of `DESIGN.md` states both
  isomorphisms for $n\ge1$, the generality in which the book's argument
  works; for $n=0$, next to them, the library proves that the fundamental
  groups are trivial, which is the counterexample. For the unitary group
  this is `Matrix.UnitaryGroup.bijective_fundamentalGroupMap_detCircle_and_simplyConnectedSpace`,
  stated for a nonempty index type, with the counterexample
  `Matrix.UnitaryGroup.subsingleton_fundamentalGroup_of_isEmpty` and
  `Matrix.UnitaryGroup.not_bijective_fundamentalGroupMap_detCircle_of_isEmpty`
  (`Analysis/Matrix/UnitaryGroup/FundamentalGroup.lean`); the simple
  connectivity of $\mathrm{SU}(n)$ holds for every $n$.
- **Issue:** #4.

## Other sources
