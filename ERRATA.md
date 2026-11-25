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
  `Matrix.UnitaryGroup.not_bijective_fundamentalGroupMap_detCircle_of_isEmpty`
  (`Analysis/Matrix/UnitaryGroup/FundamentalGroup.lean`); that the fundamental
  group is trivial for an empty index type needs no new lemma, as instance
  search derives it from the group being a point. For the symplectic group it
  is `TauCeti.GLSymplectic.nonempty_fundamentalGroup_mulEquiv_int`, with the
  isomorphism induced by `TauCeti.GLSymplectic.maslovPhase`
  (`bijective_fundamentalGroupMap_maslovPhase`), stated for a nonempty index
  type, with the counterexample
  `TauCeti.GLSymplectic.not_bijective_fundamentalGroupMap_maslovPhase_of_isEmpty`
  (`Analysis/Matrix/SymplecticGroup/FundamentalGroup.lean`); again instance
  search shows that the fundamental group is trivial for an empty index type.
  The simple connectivity of
  $\mathrm{SU}(n)$ holds for every $n$.
- **Issue:** #4.

## atlas/almost-complex-structures.md

### Hypersurfaces of degree zero are empty

- **Where:** `atlas/almost-complex-structures.md`, *Chern classes of
  projective hypersurfaces* (the Betti numbers and $b^\pm$ of
  surfaces in $\mathbb CP^3$, the Betti numbers of threefolds in
  $\mathbb CP^4$) and the example of plane curves in *Adjunction formula*.
- **Error:** the page allows any degree $d$, and its formulas for these
  numbers are stated with no bound on $d$. For $d=0$ the polynomial is a
  nonzero constant, so the hypersurface is empty and all its Betti numbers,
  its $b^\pm$ and its genus vanish. The formulas give other values: for
  the empty surface in $\mathbb CP^3$, $b_2=d^3-4d^2+6d-2=-2$ and
  $3b^+=3b^-=-3$; for the empty threefold, $b_2=b_4=1$ and $b_3=4$; for the
  empty plane curve, $g=\tfrac12(d-1)(d-2)=1$. The Chern classes,
  $\chi=d^3-4d^2+6d$ and $\sigma=\tfrac13(4-d^2)d$ do hold for $d=0$, all
  being zero.
- **Fix:** the library assumes `d ≠ 0` exactly where the formulas need
  it: `bettiNumber_two_surface`, `signature_surface`
  (`Hypersurface/Surface.lean`),
  `bettiNumber_two_threefold`, `bettiNumber_four_threefold`,
  `bettiNumber_three_threefold` (`Hypersurface/Threefold.lean`) and
  `two_mul_surfaceGenus` (`Hypersurface/PlaneCurve.lean`), all in the
  namespace `SymplecticGeometry.SmoothProjectiveHypersurface`. The Chern
  classes and `eulerChar_surface` are stated for every `d`; in
  `signature_surface` only the equations for $b^\pm$ use `d ≠ 0`. The
  counterexamples are the Fermat hypersurfaces of degree zero, which are
  empty (`instIsEmpty` in `Hypersurface/Basic.lean`): the surface has
  $b_2=0\neq-2$ (`bettiNumber_two_fermat_zero`) and $b^+=0\neq-1$
  (`sigPos_fermat_zero`), the threefold has $b_2=0\neq1$
  (`bettiNumber_two_fermat_zero_threefold`) and $b_3=0\neq4$
  (`bettiNumber_three_fermat_zero_threefold`), and the curve
  has genus $0$, while $(d-1)(d-2)=2$ (`surfaceGenus_fermat_zero`).
- **Issue:** #1148.

## atlas/symplectic-group-actions.md

### The centre of the equivariant Darboux chart is a fixed point

- **Where:** `atlas/symplectic-group-actions.md`, *Equivariant Darboux
  theorem and quadratic local moment maps*.
- **Error:** the milestone lets the point $p$ be any point of $M$, but asks
  for $G$ to act on $T_pM$ through the derivatives of its elements and for
  an equivariant $\Phi$ with $\Phi(0)=p$. Both need $g\cdot p=p$ for every
  $g$: the derivative of $g$ at $p$ maps $T_pM$ to $T_{g\cdot p}M$, and
  equivariance gives $g\cdot p=g\cdot\Phi(0)=\Phi(g\cdot 0)=\Phi(0)=p$. For
  the rotations of $S^2$ about an axis and a point $p$ off the axis, no such
  $\Phi$ exists. The sources state the theorem at a fixed point.
- **Fix:** the library states the milestone for a point fixed by $G$, the
  hypothesis of Tau Ceti's
  `TauCeti.SmoothTwoForm.IsSymplectic.exists_equivariant_darbouxChart` and
  `TauCeti.SmoothTwoForm.IsMomentMap.exists_weightModelChart`, which
  *Equivariant normal forms* translates (see `DESIGN.md`).
- **Issue:** #2247.

## atlas/constructing-symplectic-manifolds.md

### The parametric h-principle on open manifolds is a weak equivalence

- **Where:** `atlas/constructing-symplectic-manifolds.md`, *Gromov's
  h-principle for symplectic forms on open manifolds*, its parametric
  statement.
- **Error:** the page asks for the inclusion of the symplectic forms in a
  class $a$ into the nondegenerate two-forms, both in the compact-open
  $C^\infty$ topology, to be a homotopy equivalence. The proofs in the
  sources give a weak homotopy equivalence: they deform families over a
  cube, relative to its boundary (Y. Eliashberg and N. Mishachev,
  *Holonomic approximation and Gromov's h-principle*, arXiv:math/0101196,
  §2.1 and Theorem 2.1.2; M. Bertelson, *A h-principle for open relations
  invariant under foliated isotopies*, arXiv:math/0011045, Theorem 8.2,
  for a prescribed class). A weak equivalence between spaces of CW type is
  a homotopy equivalence, but when $M$ has infinitely many components, or
  is connected of infinite type, neither space need have CW type
  (`design/symplectic-h-principle.md`, Decision 5), and the step from the
  weak to the genuine equivalence is missing. No counterexample is known;
  for a connected open $M$ of infinite type the genuine equivalence is an
  open question.
- **Fix:** the library proves the weak homotopy equivalence for every open
  $M$, `isWeakHomotopyEquivalence_inclusion_symplecticFormsInClass`, which
  carries the milestone line, and, as a corollary, the homotopy equivalence
  for an $M$ each of whose components compresses into a compact set,
  `exists_homotopyEquiv_symplecticFormsInClass` (both in
  `Geometry/Symplectic/HPrinciple/Parametric.lean`).
- **Issue:** #3898.

## Other sources
