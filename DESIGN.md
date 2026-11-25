# Design

This is the overview of the library's design, as `AGENTS.md` describes it: the
parts of the library, the folders and files each part owns, the definitions
that several parts share, which parts build on which, and the part (or the
existing Mathlib or Tau Ceti declaration) that proves each milestone of the
plan. A part may have a detailed design of its own in `design/<part>.md`,
where `<part>` is the part's name below; the parts that need one are marked.

The first page of the plan that this design covers is
`atlas/linear-symplectic-geometry.md` (McDuff–Salamon [McDuffSalamon2017],
Chapter 2; for the Maslov index of paths also Robbin–Salamon
[RobbinSalamon1993]), with parts 1–13. The second is
`atlas/symplectic-manifolds.md` (McDuff–Salamon, Chapter 3, with the
auxiliary page `auxiliary/smooth-primitives.md` that it relies on), with
parts 14–21. The third is `atlas/almost-complex-structures.md`
(McDuff–Salamon, Chapter 4), with parts 22–34. The fourth is
`atlas/symplectic-group-actions.md` (McDuff–Salamon, Chapter 5, with
Cannas da Silva [CannasdaSilva2001] for the local models), with parts
35–44. The fifth is `atlas/symplectic-fibrations.md` (McDuff–Salamon,
Chapter 6, with Guillemin–Lerman–Sternberg
[GuilleminLermanSternberg1996] and Seidel [Seidel1997Thesis;
Seidel2003]), with parts 47–56, together with the auxiliary page
`auxiliary/diffeomorphisms-of-the-2-sphere.md` that it relies on, with
parts 45–46. The parts are named after
their mathematics, not after a page, so that the next pages extend them or
add parts beside them.

All statements about Tau Ceti and Mathlib below were checked, when they
were written, against the versions then pinned: at first Tau Ceti
`v4.37.0-rc1` (commit `e0e414c`) and the Mathlib it pins. Since the move
to `c9d170eed5a8` (#2025), `lakefile.toml` pins Tau Ceti `c9d170eed5a8`.
Paths of Tau Ceti files are given
relative to `.lake/packages/TauCeti/TauCeti/`.

## Principles

- **Tau Ceti is the base, not a competitor.** Tau Ceti already has most of the
  linear theory: symplectic forms, Lagrangian subspaces, Darboux bases, the
  symplectic matrix group with its polar decompositions and maximal compact
  subgroup, complex structures with compatibility and taming, the Cayley
  transform, the Maslov index of symplectic loops and of totally real loops,
  and the complex coordinate model `ι → ℂ` with its splitting
  `TauCeti.complexToRealEuclidean`. The library never redefines these
  notions. It adds the missing theorems about them, in the namespace of the
  notion they are about (`Matrix.…`, `SymplecticGroup.…`,
  `TauCeti.SymplecticForm.…`, `TauCeti.GLSymplectic.…`), so that they can move
  into Tau Ceti unchanged, and new notions in `SymplecticGeometry`.
- **One representation per notion.** Where Tau Ceti has two models of the same
  object (for example `Matrix.symplecticGroup` and `TauCeti.GLSymplectic`),
  the library states results in the model the surrounding Tau Ceti API uses,
  and does not add a third. A complex structure is always a
  `TauCeti.AlmostComplexStructure`; matrices with square $-1$ are reached only
  through a homeomorphism with it.
- **Transport rather than re-derive.** Tau Ceti states much of the theory on
  `ι → ℂ` or on `V × V`. The library's own model is reached from these by
  `complexToRealEuclidean` and `EuclideanSpace.sumEquivProd`, and the
  structures on it are defined as transports along them, so that the results
  move with them.
- **Shared definitions come first and are few.** The only part that many
  others wait for is *Standard model*, which is small (a few hundred lines)
  and has no theorems of substance. Everything else can be built in parallel
  once its direct prerequisites are merged; the graph below has depth at most
  five.
- **Files do not clash with Tau Ceti's.** A folder of this library never has
  the name of a Tau Ceti file at the same place (no `Foo/` here beside Tau
  Ceti's `Foo.lean`), so that both can move upstream as they are. A file of
  this library may have the name of a Tau Ceti file: upstream, the two merge.

## Conventions

The library uses McDuff–Salamon's conventions for the linear theory. Each
convention is fixed by a lemma, mostly of *Standard model*, and later parts
rewrite with that lemma rather than recompute a sign. The plan's sign
conventions for manifolds (`auxiliary/02-signs.md`) concern Hamiltonian
vector fields and moment maps, which the linear theory does not use; for the
parts of later pages see *Manifolds, families and signs* and *Group actions,
moment maps and periods* below.

- **The model space.** `StdSpace ι` is `EuclideanSpace ℝ (ι ⊕ ι)` for a finite
  type `ι` (usually `Fin n`), with `StdSpace.x z i = z (Sum.inl i)` and
  `StdSpace.y z i = z (Sum.inr i)`. Three reasons fix this choice. Mathlib
  indexes `Matrix.J ι ℝ` and `Matrix.symplecticGroup ι ℝ` by `ι ⊕ ι`, so a
  matrix acts on the model through `Matrix.toEuclideanLin` with no
  reindexing. Tau Ceti's `complexToRealEuclidean ι : (ι → ℂ) ≃L[ℝ]
  StdSpace ι` lands in it, real parts at `inl`, imaginary parts at `inr`. And
  its norm is the Euclidean norm of all $2n$ coordinates. The norm of a Lean
  product `E × F` is the larger of the two norms, so metric statements
  (balls, cylinders, ellipsoids, widths) are never made on
  `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι`.
- **$\omega_0$ and $J_0$.** `stdForm ι` and `stdComplexStructure ι` are the
  transports of `TauCeti.stdComplexPiSymplecticForm ι` and of multiplication
  by `I` on `ι → ℂ` along `complexToRealEuclidean ι`. *Standard model* proves:
  `stdForm_apply`, $\omega_0(z,w)=\sum_i(x_i(z)y_i(w)-y_i(z)x_i(w))$;
  `stdComplexStructure_x` and `stdComplexStructure_y`, $x(J_0z)=-y(z)$ and
  $y(J_0z)=x(z)$, that is, $J_0$ is `Matrix.toEuclideanLin (Matrix.J ι ℝ)`;
  `stdForm_apply_eq_inner`, $\omega_0(z,w)=\langle J_0z,w\rangle$; and
  `stdForm_toBilinForm`, that $\omega_0$ is `-Matrix.toBilin' (Matrix.J ι ℝ)`
  read through `WithLp`. For `ι = Fin n` the last one says that Tau Ceti's
  `stdSymplecticBilinForm ℝ n` is $-\omega_0$.
- **The symplectic group.** Mathlib's membership condition is $AJA^T=J$. The
  condition that $A$ preserves $\omega_0$, $A^TJA=J$, is
  `SymplecticGroup.mem_iff'`, and *Standard model*'s
  `mem_symplecticGroup_iff_isSymplectomorphism` turns either into a statement
  about `Matrix.toEuclideanLin A`. Topological statements (paths, loops,
  homotopies, the Maslov index) use Tau Ceti's subgroup
  `TauCeti.GLSymplectic ι ℝ` of `GL (ι ⊕ ι) ℝ`, as Tau Ceti's Maslov index
  does.
- **Bases from a Gram matrix.** The `(inr i, inl j)` entry of `Matrix.J` is
  $\delta_{ij}$ and the `(inl i, inr j)` entry is $-\delta_{ij}$. So for a
  basis `b` with `Matrix.J` as Gram matrix, the pairs of the book with
  $\omega(u_j,v_k)=\delta_{jk}$ are $u_j=$ `b (inr j)` and $v_j=$ `b (inl j)`.
  Tau Ceti's `TauCeti.SymplecticForm.IsDarbouxBasis` is already in the book's
  normalization. A statement that produces a basis says in its docstring which
  of the two it uses.
- **Tau Ceti's objects with another sign or factor.** Tau Ceti's definitions
  are used as they are. A milestone that involves one of them is stated with
  the book's object, written as `-` or `2⁻¹ •` of Tau Ceti's, not as a new
  definition:

  | Tau Ceti | The book's object |
  |---|---|
  | `TauCeti.stdSymplecticBilinForm` | $-$ it is $\omega_0$ (see above) |
  | `TauCeti.SymplecticForm.twistedProd` | $-$ it is $(-\omega_1)\oplus\omega_2$; the Lagrangians agree, Maslov indices of loops change sign |
  | `TauCeti.SymplecticForm.symmetrizedBilinForm` | $2^{-1}$ times it is $g_{\omega,J}$ |
  | the Cayley transform of a tame $J$ (`Geometry/Symplectic/Cayley/`) | $-$ it is the book's $W$ |

- **Polar decompositions.** Tau Ceti has both. `Units.polarUnitary_mul_sqrt_star_mul`
  (`Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Polar.lean`) is the
  right decomposition $A=U\sqrt{A^*A}$ in any C*-algebra, with uniqueness
  `Units.mul_eq_iff_polarUnitary_eq_and_sqrt_star_mul_eq`; for matrices,
  `SymplecticGroup.polarUnitary_mem` and `SymplecticGroup.sqrt_mul_star_mem`
  (`Analysis/Matrix/Polar/Symplectic.lean`) say that the unitary factor and
  the factor $\sqrt{AA^*}$ of a symplectic $A$ are symplectic. The book's $U$
  is `Units.polarUnitary`.
- **Maslov indices.** The normalizations are the book's: the loop
  $t\mapsto e^{2\pi it}$ of $\mathrm{U}(1)$ has index $1$, and so has the loop
  $t\mapsto e^{\pi it}\mathbb{R}$ in $\mathcal{L}(1)$. If a later part defines
  the Robbin–Salamon index for paths of matrices in $\mathrm{Sp}(2n)$, which on loops is
  twice the book's index, its name and docstring say so.
- **Loops and homotopies.** A loop is a `Path x x` on the unit interval, as in
  Tau Ceti. Homotopy of loops means free homotopy through loops (a continuous
  `F : I × I → X` with `F (s, 0) = F (s, 1)`), the hypothesis of Tau Ceti's
  `TauCeti.GLSymplectic.maslovIndex_eq_of_homotopy`. The *Maslov index* part
  fixes the predicate for it, reusing Tau Ceti's free loop spaces in
  `Topology/MappingSpace/FreeLoop.lean` if they fit.
- **Exterior powers.** $\omega^n$ is Tau Ceti's
  `ContinuousAlternatingMap.wedgePow`, which is $n!$ on a Darboux basis.

### Manifolds, families and signs

These conventions serve parts 14–21. The parts use Tau Ceti's manifold
objects as they are.

- **Manifolds.** A manifold is modelled by `I : ModelWithCorners ℝ E H` with
  `[FiniteDimensional ℝ E]` and `[IsManifold I ∞ M]`. Hausdorffness, second
  countability and `[I.Boundaryless]` (or `[BoundarylessManifold I M]`) are
  added where a statement needs them, as Tau Ceti does. Manifolds with
  boundary occur only in the strong fillings of *Liouville structures*.
- **Forms.** A symplectic form is `ω : TauCeti.SmoothTwoForm I M` with
  `ω.IsSymplectic` (closed, `ω.IsNondegenerate`). One-forms and functions are
  `TauCeti.SmoothForm I M ℝ 1` and `C^∞⟮I, M; ℝ⟯`. There is no bundled type of
  symplectic manifolds, as there is none in Tau Ceti.
- **Families and isotopies.** Tau Ceti has two models, and the library adds
  no third.
  - *Over $[0,1]$*, as the plan's families are: the cylinder
    `unitInterval × M`, with Mathlib's manifold-with-boundary structure on
    the interval. A smooth family of $k$-forms is a smooth form on it, read
    through its slices; an isotopy of $M$ is Tau Ceti's
    `TauCeti.Diffeotopy I ∞ M` (`Geometry/Diffeomorphism/Diffeotopy/Basic.lean`);
    a family of embeddings is Tau Ceti's `TauCeti.SmoothIsotopy`
    (`Geometry/Manifold/SmoothIsotopy/Basic.lean`). Symplectic and
    Hamiltonian isotopies, isotopy extension, and every milestone about a
    family are stated in this model, except the rescaling formula for the
    flow of a time-dependent contact Hamiltonian (*Contact geometry*),
    which is about the maximal flow wherever it is defined and is stated
    over `ℝ`, on Tau Ceti's `TauCeti.timeDependentFlowDomain`. A milestone about isotopies also
    applies to a jointly smooth map on `unitInterval × M` that is the
    identity at time $0$ and whose slices are diffeomorphisms, through the
    constructor of `Diffeotopy/OfContMDiff.lean` that makes it a `Diffeotopy`.
  - *Over `ℝ`*, the model of Tau Ceti's Moser and Gray theorems
    (`Geometry/Symplectic/Manifold/Moser.lean`): a smooth form on `ℝ × M`
    read through `SmoothForm.mpullback (Prod.mk t) _`, a time-dependent
    vector field `ℝ × M → TM` with flow `TauCeti.timeDependentFlowOf`, and an
    isotopy `ψ : ℝ → M ≃ₘ⟮I, I⟯ M`, jointly smooth with `ψ 0 = id`, whose
    generator is `TauCeti.eulerianField`. It is used only inside proofs that
    call that API.

  The files `ContMDiff/TimeExtension.lean`,
  `DifferentialForm/TimeExtension.lean` and `Diffeotopy/Real.lean` of
  *Smooth families* pass between them. A family over $[0,1]$
  extends to one over `ℝ` (Seeley's extension in the time variable), an
  isotopy over `ℝ` restricts to a `Diffeotopy`, and a `Diffeotopy` is read
  over `ℝ` by reparametrization; for flows Tau Ceti already
  has `TauCeti.timeDependentFlowDiffeotopy`. A proof that needs its
  hypotheses for every real time extends the family past both ends. When the
  support is compact, the open conditions (symplectic, contact) still hold on
  some $(-\varepsilon,1+\varepsilon)$. The proof then reparametrizes by a
  smooth map $\mathbb{R}\to(-\varepsilon,1+\varepsilon)$ that is the identity
  on $[0,1]$, so the isotopy it gets is the wanted one on all of $[0,1]$.
  `Real.smoothTransition` is flat at $0$ and $1$, so a reparametrization by
  it cannot be undone smoothly there. It is used for conclusions about the
  time-one map, as in Tau Ceti's relative Moser theorem, and for statements
  about every time of a `Diffeotopy` $\Phi$: with
  $s=$ `Real.smoothTransition`, $t\mapsto\Phi_{s(t)}$ is an isotopy over
  `ℝ` with generator $s'(t)X_{s(t)}$. As $s'>0$ on $(0,1)$ and $s'=0$
  elsewhere, a linear condition on the generator that passes to limits,
  such as closedness of $\iota_{X_t}\omega$, holds at every real time
  exactly when it holds for $X_t$ at every $t\in[0,1]$, the ends following
  by continuity.
- **Submanifolds.** An embedded submanifold is the image of Tau Ceti's
  `SmoothEmbedding J I ∞ Q M`. *Compact* is `[CompactSpace Q]`, *properly
  embedded* is `IsClosed (Set.range f)`. Its type is one of Tau Ceti's
  predicates `TauCeti.SmoothTwoForm.IsNondegenerate.IsSymplecticSubmanifoldEmbedding`,
  `IsIsotropicEmbedding`, `IsLagrangianEmbedding` and `IsCoisotropicEmbedding`.
- **Neighbourhood germs.** A map between neighbourhoods of submanifolds is a
  diffeomorphism `U₀ ≃ₘ⟮I, I⟯ U₁` between `U₀ U₁ : Opens M`, with the forms
  restricted along `Subtype.val`, the form of Tau Ceti's
  `TauCeti.SmoothTwoForm.exists_diffeomorph_opens_of_eq_along`. A chart is a
  `PartialDiffeomorph`, as in Tau Ceti's Darboux theorems.
- **Signs.** `atlas/symplectic-manifolds.md` states its milestones in
  McDuff–Salamon's signs, not in those of `auxiliary/02-signs.md` (see
  *Departures*). The library uses Tau Ceti's and Mathlib's objects as they
  are, and states each milestone with the page's object, written through
  them as the table says. No new definition is made for a sign change.

  | The page's object | Tau Ceti or Mathlib | In the statements |
  |---|---|---|
  | $X_H$ with $\iota_{X_H}\omega=dH$ | `TauCeti.SmoothTwoForm.IsHamiltonianVectorField`, `hamiltonianVectorField` | as it is |
  | the book's bracket $[X,Y]_{\mathrm b}$ of vector fields | Mathlib's `VectorField.mlieBracket`, the usual bracket | `-mlieBracket` |
  | $\{F,G\}=\omega(X_F,X_G)$ | `TauCeti.SmoothTwoForm.poissonBracket` | as it is |
  | $\lambda_{\mathrm{can}}$, $\omega_{\mathrm{can}}=-d\lambda_{\mathrm{can}}$ on $T^*L$ | `TauCeti.CotangentBundle.liouvilleForm`, `symplecticForm` | as they are |
  | contact Hamiltonian $X_H$ | `TauCeti.SmoothForm.contactHamiltonianVectorField` | as it is |
  | $\sum_ip_i\,dq_i-dz$ | `TauCeti.innerProductContactForm`, which is $dz-\sum_ip_i\,dq_i$ | `-innerProductContactForm V`, equal to its pullback by $(q,p,z)\mapsto(q,-p,-z)$ (`mpullback_innerProductContactForm_neg`) |
  | the symplectization form $-d(e^s\alpha)$ on $\mathbb{R}\times M$ | `TauCeti.SmoothForm.symplectization α`, which is $e^t\alpha$ | $-d$ of it |
  | the contact form $-i^*(\iota_Y\omega)$ of a hypersurface of contact type | `TauCeti.IsContactType`, whose primitive $\lambda$ has $d\lambda=\omega$ and $\iota_Z\omega=\lambda$ | $-i^*\lambda$, with $Y=Z$ |

### Almost complex structures, Kähler manifolds and characteristic classes

These conventions serve parts 22–34, for `atlas/almost-complex-structures.md`.
The parts use Tau Ceti's objects as they are, and state each milestone in the
page's conventions through them.

- **Almost complex structures.** The library writes $J$ on $M$ as
  Tau Ceti's `TauCeti.SmoothAlmostComplexStructure I M`, tameness and
  compatibility with a two-form are `TauCeti.SmoothTwoForm.Tames` and
  `Compatible`, and the spaces $\mathcal J(M)$, $\mathcal J(M,\omega)$,
  $\mathcal J_\tau(M,\omega)$ are the type and its subtypes, with Tau Ceti's
  `frameTopology` (the compact-open $C^\infty$ topology), as part 12 does for
  bundles. The two-form $\omega$ of §§4.1–4.2 is only assumed nondegenerate
  (`IsNondegenerate`); a statement that needs $d\omega=0$ says so. As in Tau
  Ceti, $M$, $J$, $\omega$ and $g$ stay separate arguments; no structure
  bundles them.
- **The metric.** For a compatible pair, $g_J(v,w)=\omega(v,Jw)$, the
  page's convention and Tau Ceti's (`TauCeti.SymplecticForm.associatedBilinForm`).
  As a Riemannian metric on $TM$ it is part 12's `Compatible.metric` read on
  the tangent bundle (*Almost complex manifolds*). Mathlib's Levi-Civita
  connection `CovariantDerivative.leviCivitaConnection` takes its metric from
  a `RiemannianBundle` instance; the parts install $g_J$ as a local instance
  inside the statements that need its connection.
- **Brackets, $d$ and the Nijenhuis tensor.** Mathlib's `mlieBracket` is the
  usual bracket, the negative of the book's (as in the table of *Manifolds,
  families and signs*). With it, Tau Ceti's
  `TauCeti.SmoothAlmostComplexStructure.nijenhuis`, which is
  $[JX,JY]-[X,Y]-J[JX,Y]-J[X,JY]$ for the usual bracket, is exactly the
  book's $N_J$, with no sign and no factor, and Tau Ceti's
  `TauCeti.SmoothForm.mextDeriv_apply_two` is the book's formula for $d$ of a
  two-form. A torsion-free connection in Mathlib's sense
  ($\nabla_XY-\nabla_YX=$ `mlieBracket X Y`) is torsion free in the book's.
  For an endomorphism field such as $J$, $\nabla J$ is Tau Ceti's Hom
  connection `CovariantDerivative.hom` applied to its section.
- **Integrable and Kähler.** *Integrable* is the book's notion, an atlas in
  which $J$ is constant (*Nijenhuis tensor* defines the predicate). Tau
  Ceti's `TauCeti.SmoothTwoForm.IsKahler` asks for $N_J=0$ instead of
  integrability. The library states with `IsKahler` every result whose proof
  uses only $N_J=0$, as the page advises, and adds the integrability
  predicate only where charts are needed (*Hodge theory*, the integrable
  case of *Complex submanifolds*). A later proof of the integrability theorem
  then turns the first kind into the book's statements without changing
  them.
- **Complex projective space.** $\mathbb CP^n$ is
  `ℙ ℂ (Fin (n + 1) → ℂ)`, the type of Mathlib, carrying the complex
  manifold structure of Tau Ceti
  (`Geometry/Manifold/Instances/Projectivization.lean`), on which Tau Ceti
  has zero loci, the line bundles `Projectivization.twistCore` and the
  Lefschetz theorems; its almost complex structure is
  `SmoothAlmostComplexStructure.ofComplexManifold`. Tau Ceti's sphere
  quotient `TauCeti.ComplexProjectiveSpace n`, which carries the cohomology,
  is reached by Tau Ceti's homeomorphism between the two models. The
  Fubini–Study form has the page's normalization, area $\pi$ on a line; Tau
  Ceti's `OnePoint.fubiniStudyForm` on $\mathbb CP^1$ has area $1$, so on
  $\mathbb CP^1$ the page's form is $\pi$ times its pull-back.
- **Energy.** The operator is
  $\bar\partial_J(u)=\tfrac12(du+J\circ du\circ j)$, the energy
  $E(u)=\tfrac12\int_\Sigma\lvert du\rvert^2$, as on the page. A closed
  Riemann surface is a closed surface with a
  `SmoothAlmostComplexStructure` $j$, oriented by $j$; by the milestone on
  surfaces this loses nothing.
- **Characteristic classes and Betti numbers.** Chern classes are integral
  singular cohomology classes (`TauCeti` singular cohomology with chain
  coefficients `ULift ℤ`), $c_1$ being *First Chern number*'s
  `SymplecticGeometry.Bundle.firstChernClass`, with values in `ULift ℤ`.
  *Chern classes* takes values in `ℤ` (`TopCat.integralCohomology`, whose
  cup product has the ring laws) and compares with classes valued in
  `ULift ℤ` through an isomorphism, as `design/chern-classes.md` says.
  The fundamental class and
  the evaluation $\langle c,[M]\rangle$ are Tau Ceti's
  `TauCeti.HomologicalOrientation.fundamentalClass` and
  `evalFundamentalClass`. A complex manifold, or a manifold with an almost
  complex structure, is oriented by its complex structure (Tau Ceti's
  `TauCeti.complexManifoldOrientation`, `VectorBundleOrientation.complex`).
  Betti numbers in the Hodge milestone are dimensions of Tau Ceti's de Rham
  cohomology (`TauCeti.deRhamCohomology`, `complexDeRhamCohomology`), the
  form in which the book and Tau Ceti's Kodaira–Thurston files use them;
  in the hypersurface milestone they are ranks of singular homology
  (`TauCeti.bettiNumber`).

### Group actions, moment maps and periods

These conventions serve parts 35–44, for `atlas/symplectic-group-actions.md`,
and the parts that `atlas/symplectic-fibrations.md` adds on top of *Lie
group actions* and *Moment maps*. The parts use Tau Ceti's objects as they
are, and state each milestone in the page's conventions through them.

- **Actions.** A Lie group is `G` with `[LieGroup I ∞ G]` on a
  finite-dimensional boundaryless model; its Lie algebra is
  `GroupLieAlgebra I G` and its exponential `mulInvariantExp`. A smooth
  left action is `[MulAction G M] [ContMDiffSMul I I' ∞ G M]`. Its
  fundamental vector field $X_\xi$, the velocity of
  $t\mapsto\exp(t\xi)\cdot p$ at $0$, is Tau Ceti's
  `TauCeti.fundamentalVectorField`, packaged as the infinitesimal action
  `TauCeti.InfinitesimalAction.fundamental I G I' M`. Mathlib's
  `VectorField.mlieBracket` is the page's bracket, so here, unlike on
  `atlas/symplectic-manifolds.md`, no bracket is negated, and Tau Ceti's
  `TauCeti.InfinitesimalAction` already has the page's relation
  $X_{[\xi,\eta]}=-[X_\xi,X_\eta]$. A symplectic action is the hypothesis
  that every `g • ·` pulls $\omega$ back to itself, as in Tau Ceti's
  theorems; there is no predicate for it.
- **The Hamiltonian sign.** The page uses the sign of
  `auxiliary/02-signs.md`, $\iota_{X_H}\omega=-dH$, and Tau Ceti the
  opposite one. For the same $\omega$ the page's moment map $\mu$ is
  `fun x ↦ -μ x` for Tau Ceti's predicates: the milestones are stated with
  `ω.IsMomentMap a (fun x ↦ -μ x)` and
  `ω.IsEquivariantMomentMap (fun x ↦ -μ x)` (equivariance is linear, so it
  is the page's equivariance of $\mu$), and `IsMomentMap.neg` passes to
  `(-ω).IsMomentMap a μ` where a proof prefers it. The page's $X_H$ is
  `TauCeti.SmoothTwoForm.hamiltonianVectorField` of $-H$, as the
  departure on `atlas/symplectic-manifolds.md` already says. The Poisson
  bracket `TauCeti.SmoothTwoForm.poissonBracket` is the page's, and Tau
  Ceti's `momentCocycle` of $-\mu$ is the page's cocycle $\tau$. A level
  $\mu^{-1}(c)$ of the page is Tau Ceti's level at $-c$; the zero level is
  the same. Tau Ceti's `Module.Dual.coadjointOrbitForm` is the page's orbit
  form, with the orbit map as moment map in Tau Ceti's sign, so minus the
  orbit map in the page's. No new definition is made for a sign change.
- **Periods.** Circle parameters have period one. A circle action is an
  action of Mathlib's `Circle`, whose parameter $t\in\mathbb R/\mathbb Z$
  acts as `Circle.exp (2 * π * t)`. Its generator is
  $\xi_1=2\pi\cdot$ `circleLieGenerator` (`Geometry/Lie/Exponential/Circle.lean`,
  whose exponential is `Circle.exp`, of period $2\pi$), and the page's
  Hamiltonian is $H=\langle\mu,\xi_1\rangle$. A torus is a compact
  connected commutative Lie group, the hypotheses of Tau Ceti's
  `MomentMap/ConvexHull.lean`. Tau Ceti's weights $\alpha^{\mathrm{TC}}$
  have $\chi(\exp\xi)=$ `Circle.exp (α ξ)`; the page's weights are
  $\alpha=\alpha^{\mathrm{TC}}/2\pi$. With $\mu=-\mu^{\mathrm{TC}}$, Tau
  Ceti's quadratic form $\mu^{\mathrm{TC}}(p)-\tfrac12\sum_j|z_j|^2
  \alpha^{\mathrm{TC}}_j$ is the page's $\mu(p)+\pi\sum_j|z_j|^2\alpha_j$.
- **Kähler.** The Kähler manifolds of the last two milestones are Tau
  Ceti's `TauCeti.SmoothTwoForm.IsKahler` pairs, as in parts 22–34; where
  a proof needs holomorphic charts, *Kähler stability*'s design file says
  which hypothesis it adds.

### Fibrations, connections and diffeomorphism groups

These conventions serve parts 45–56, for `atlas/symplectic-fibrations.md`
and `auxiliary/diffeomorphisms-of-the-2-sphere.md`. The fibrations page
takes its signs from `auxiliary/02-signs.md`, as
`atlas/symplectic-group-actions.md` does, so the rules of *Group actions,
moment maps and periods* hold here unchanged: the page's $X_H$ is
`hamiltonianVectorField` of $-H$, its $\mu$ is minus Tau Ceti's, and no
bracket is negated.

- **Fibrations.** A fibration with fibre $F$ is given by `π : M → B`, smooth,
  of manifolds with local trivializations `e : Bundle.Trivialization F π`
  (Mathlib) that are smooth with smooth inverses between
  `π ⁻¹' e.baseSet` and `e.baseSet ×ˢ univ`. Tau Ceti's smooth fibre
  bundles (`TauCeti.ContMDiffFiberBundle`, charted by
  `TauCeti.ManifoldTotalSpace`) and associated bundles
  (`TauCeti.AssociatedBundle`) are fibrations in this sense, by a bridge
  that *Symplectic fibrations* proves once, so that milestones stated for
  a given manifold $M$ apply to them. A structure group
  $H\le\mathrm{Diff}(F)$ is an atlas of trivializations covering $B$ whose
  coordinate changes lie in $H$ at each base point; no topology on $H$ is
  used. The fibre over $b$ is read through a chart $e$ of the atlas, as
  the embedding $v\mapsto e^{-1}(b,v)$ of $F$ into $M$; Tau Ceti's
  `TauCeti.ManifoldTotalSpace.fiberChartedSpace`, or for the fibre of a
  submersion `TauCeti.regularFiberChartedSpace`, is used only where a
  statement needs a fibre as a manifold of its own.
- **Fibre forms.** As the page's formalization note allows, a symplectic
  fibration is a fibration with an atlas for $(F,\sigma)$ whose coordinate
  changes lie in `TauCeti.SmoothForm.diffeomorphStabilizer σ`, and the fibre
  forms $\sigma_b$ are not data. A form $\tau$ on $M$ *restricts to the
  fibre forms* when it pulls back to $\sigma$ along $v\mapsto e^{-1}(b,v)$
  for every chart $e$ of the atlas and every $b$ in its base set.
  Compatible symplectic forms, connection 2-forms and coupling forms are
  stated with this predicate.
- **Connections.** A connection on a fibration is Tau Ceti's
  `TauCeti.IsEhresmannConnection` on `π`
  (`Geometry/Manifold/Submersion/EhresmannConnection.lean`) with its
  pointwise `horizontalLift`. Its curvature is the page's
  $\Omega_\Gamma(v_1,v_2)=[v_1^\sharp,v_2^\sharp]^{\mathrm{Ver}}$ with
  Mathlib's `VectorField.mlieBracket`, which is the page's bracket. The
  holonomy around a loop at $b$ is read in a chart $e$ of the atlas at
  $b$, as a diffeomorphism of $F$. It is *Hamiltonian* when that
  diffeomorphism lies in `TauCeti.SmoothForm.hamiltonianGroup σ`; the chart
  does not matter, since that group is normal among the symplectomorphisms
  (`TauCeti.SmoothForm.normal_hamiltonianGroup_subgroupOf_diffeomorphStabilizer`).
- **Principal connections.** Principal bundles are Tau Ceti's
  `TauCeti.PrincipalBundle`, whose right action is an action of the
  opposite group, with the fundamental fields $p\xi$ of
  `TauCeti.PrincipalBundle.rightFundamentalLinearMap`. The Lie algebra is
  Mathlib's `GroupLieAlgebra I G`, whose bracket is that of left-invariant
  fields; so $[p\xi,p\eta]=p[\xi,\eta]$, and the page's $F_A(X,Y)=-A([X,Y])$
  on horizontal fields holds with `mlieBracket`. The library's circle
  connection forms (`SymplecticGeometry.IsCircleConnectionForm`) are real
  valued and normalized on `circleLieGenerator`; *Principal connections*
  proves the comparison with its connection forms for `G = Circle` and
  keeps them.
- **Flux and cohomology.** The flux is Tau Ceti's `TauCeti.Diffeotopy.flux`
  and the flux group `TauCeti.fluxGroup`
  (`Geometry/Symplectic/Flux/Endpoint.lean`), with the page's sign. Real
  cohomology is de Rham cohomology (`TauCeti.deRhamCohomology`), as on the
  page. Integral classes ($H_1(B;\mathbb Z)$, the Euler number of a circle
  bundle) are singular, and are compared with de Rham classes by Tau Ceti's
  integration map (`Geometry/Manifold/SmoothSingular/DeRham.lean`). The
  real first Chern class of the vertical bundle is a de Rham class, built
  by Chern–Weil in *Compatible symplectic forms*, and compared with the
  library's integral `SymplecticGeometry.Bundle.firstChernClass` there
  over closed oriented surfaces, through Chern numbers.
- **Diffeomorphism groups.** $\mathrm{Diff}(M)$ is Tau Ceti's `TauCeti.Diff`
  with the weak Whitney topology (`Diffeomorph.weakWhitneyTopology`,
  `Geometry/Diffeomorphism/Topology.lean`), which for a compact source is
  the $C^\infty$ topology of the auxiliary page, and a topological group
  there (`Diffeomorph.isTopologicalGroup`). $S^2$ is the Riemann sphere
  `OnePoint ℂ` with Tau Ceti's complex manifold structure, compared with
  the unit sphere of `EuclideanSpace ℝ (Fin 3)` by stereographic projection
  where `TauCeti.orthogonalToDiffSphere` is used. The space $\mathcal J$ of
  almost complex structures compatible with the orientation is the subtype
  of `TauCeti.SmoothAlmostComplexStructure` tamed by one area form, in Tau
  Ceti's `frameTopology`; on a surface the two conditions agree.
- **Cotangent model of the Dehn twist.** The page's $T^*S^n$, the set
  $\{|q|=1,\ \langle q,p\rangle=0\}$ of
  $\mathbb R^{n+1}\times\mathbb R^{n+1}$ with
  $\omega_{\mathrm{can}}=d\lambda_{\mathrm{can}}$, is Tau Ceti's cotangent
  bundle of the sphere, read in these coordinates through a smooth
  injective map onto that set (`design/dehn-twists.md`). Tau Ceti's cotangent
  bundles carry $-d\lambda$, so the Lagrangian neighbourhood theorem of
  *Symplectic neighbourhoods* is composed with $(q,p)\mapsto(q,-p)$, as
  the page's formalization note says.

## Shared definitions

These notions are used by several parts. All are reused from Tau Ceti or
Mathlib, except the three definitions of *Standard model* and the bundle
complex structures of *Symplectic vector bundles*, which *First Chern number*
also uses, the first Chern class of *First Chern number*, the
integrability predicate of *Nijenhuis tensor*, and the fibrations,
parallel transport, principal connections and fibre integrals of parts
47, 48, 50 and 51.

| Notion | Representation | Where |
|---|---|---|
| Symplectic vector space $(V,\omega)$ over $\mathbb{R}$ | `[AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (ω : TauCeti.SymplecticForm V)` | Tau Ceti |
| Symplectic form over a field `k` | `ω : LinearMap.BilinForm k V` with `ω.IsAlt` and `ω.Nondegenerate` | Mathlib |
| $\omega_0$ on $k^{2n}$ | `-TauCeti.stdSymplecticBilinForm k n` | Tau Ceti |
| $W^\omega$; isotropic, coisotropic, symplectic, Lagrangian subspaces | `TauCeti.SymplecticForm.orthogonal`, `IsIsotropic`, `IsCoisotropic`, `IsSymplectic`, `IsLagrangian` | Tau Ceti |
| Linear symplectomorphism | `TauCeti.SymplecticForm.IsSymplectomorphism` | Tau Ceti |
| $\mathrm{Sp}(2n)$ | `Matrix.symplecticGroup ι ℝ`; as a topological group `TauCeti.GLSymplectic ι ℝ` | Mathlib, Tau Ceti |
| $\mathrm{U}(n)$ inside $\mathrm{Sp}(2n)$ | `Matrix.unitaryGroup ι ℂ` with `Matrix.realify`, `TauCeti.GLSymplectic.ofUnitary` | Mathlib, Tau Ceti |
| Linear complex structure, with its topology | `TauCeti.AlmostComplexStructure V` (topology in `Geometry/Symplectic/AlmostComplex/Topology.lean`) | Tau Ceti |
| Compatible, tame | `TauCeti.SymplecticForm.Compatible`, `TauCeti.SymplecticForm.Tames` | Tau Ceti |
| $J_{g,\omega}$ (ambient $g$) | `TauCeti.SymplecticForm.polarComplexStructure` | Tau Ceti |
| $\mathbb{C}^n\cong\mathbb{R}^{2n}$ | `TauCeti.complexToRealEuclidean` (`Analysis/Complex/Euclidean/Space.lean`) | Tau Ceti |
| Degree of a circle loop | `Circle.degree` (`Topology/Circle/Degree.lean`) | Tau Ceti |
| Maslov index of a symplectic loop | `TauCeti.GLSymplectic.maslovIndex` (`Analysis/Matrix/SymplecticGroup/Maslov.lean`) | Tau Ceti |
| Continuous complex structure on a real vector bundle | `TauCeti.Bundle.ContinuousComplexStructure` (`Topology/VectorBundle/Complex/Structure.lean`) | Tau Ceti |
| $C^n$ complex structure on a smooth real vector bundle, with its topology | `SymplecticGeometry.Bundle.ContMDiffComplexStructure`, generalizing `TauCeti.ContMDiffAlmostComplexStructure I n M` with its field names and its `n`, mapping to the continuous one; on $TM$ identified with `ContMDiffAlmostComplexStructure` for every $n$, and with `TauCeti.SmoothAlmostComplexStructure` through `smoothEquiv` | *Symplectic vector bundles* |
| Bundle metrics $\mathrm{Met}(E)$, with their topology | `Bundle.ContMDiffRiemannianMetric` with Tau Ceti's `frameTopology` (`Geometry/Manifold/VectorBundle/Riemannian/SectionTopology.lean`) | Mathlib, Tau Ceti |
| $\mathbb{R}^{2n}$, $\omega_0$, $J_0$ | `SymplecticGeometry.StdSpace ι`, `SymplecticGeometry.stdForm ι`, `SymplecticGeometry.stdComplexStructure ι` | *Standard model* |
| Symplectic form on a manifold, $X_H$, $\{F,G\}$ | `ω : TauCeti.SmoothTwoForm I M` with `ω.IsSymplectic`; `TauCeti.SmoothTwoForm.hamiltonianVectorField`, `poissonBracket` | Tau Ceti |
| Smooth families over $[0,1]$: of forms, isotopies, isotopies of embeddings | forms on `unitInterval × M` read through their slices; `TauCeti.Diffeotopy I ∞ M`; `TauCeti.SmoothIsotopy` (see *Manifolds, families and signs*) | Tau Ceti |
| Families over `ℝ`, inside proofs: time-dependent flows, isotopies and their generators | forms on `ℝ × M`; `TauCeti.timeDependentFlowOf`; `ψ : ℝ → M ≃ₘ⟮I, I⟯ M` with `TauCeti.eulerianField`; passage to `Diffeotopy` in *Smooth families* | Tau Ceti |
| Symplectomorphism group | `TauCeti.SmoothForm.diffeomorphStabilizer ω : Subgroup (M ≃ₘ⟮I, I⟯ M)` | Tau Ceti |
| Symplectic, isotropic, Lagrangian, coisotropic submanifolds | `TauCeti.SmoothEmbedding` with `TauCeti.SmoothTwoForm.IsNondegenerate.IsSymplecticSubmanifoldEmbedding`, `IsIsotropicEmbedding`, `IsLagrangianEmbedding`, `IsCoisotropicEmbedding` | Tau Ceti |
| $\lambda_{\mathrm{can}}$, $\omega_{\mathrm{can}}$ on $T^*L$ | `TauCeti.CotangentBundle.liouvilleForm`, `TauCeti.CotangentBundle.symplecticForm` | Tau Ceti |
| Contact form, Reeb field, contact Hamiltonian | `TauCeti.SmoothForm.IsContactForm`, `reebVectorField`, `contactHamiltonianVectorField` | Tau Ceti |
| Liouville vector field, hypersurface of contact type | `TauCeti.IsLiouvilleVectorField`, `TauCeti.IsContactType` | Tau Ceti |
| Hamiltonian isotopy, its Hamiltonian along the motion, $\mathrm{Ham}(M,\omega)$ | `TauCeti.Diffeotopy.IsHamiltonian`, `TauCeti.Diffeotopy.HasHamiltonian`, `TauCeti.SmoothForm.hamiltonianGroup` (`Geometry/Symplectic/Flux/Hamiltonian.lean`) | Tau Ceti |
| Almost complex structure on $M$, $\mathcal J(M,\omega)$, $\mathcal J_\tau(M,\omega)$ | `TauCeti.SmoothAlmostComplexStructure I M` with `frameTopology`; subtypes for `TauCeti.SmoothTwoForm.Compatible`, `Tames` | Tau Ceti |
| Nijenhuis tensor, Kähler pair | `TauCeti.SmoothAlmostComplexStructure.nijenhuis`, `TauCeti.SmoothTwoForm.IsKahler` | Tau Ceti |
| Integrable almost complex structure | `TauCeti.SmoothAlmostComplexStructure.IsIntegrable` | *Nijenhuis tensor* |
| First Chern class of a complex bundle | `SymplecticGeometry.Bundle.firstChernClass` | *First Chern number* |
| Lie group action, fundamental vector fields $X_\xi$ | `[LieGroup I ∞ G] [ContMDiffSMul I I' ∞ G M]`; `TauCeti.fundamentalVectorField`, `TauCeti.InfinitesimalAction.fundamental` (see *Group actions, moment maps and periods*) | Mathlib, Tau Ceti |
| Moment map, equivariant moment map, its cocycle | `TauCeti.SmoothTwoForm.IsMomentMap`, `IsEquivariantMomentMap`, `momentCocycle`, applied to $-\mu$ | Tau Ceti |
| Average of a form over a compact group | `TauCeti.SmoothForm.measureAverage` with `TauCeti.haarProb` (`Geometry/Manifold/DifferentialForm/Average.lean`) | Tau Ceti |
| Quotient manifold of a free proper action | `ProperSMul.orbitRelQuotientChartedSpace`, `ProperSMul.instIsManifoldOrbitRelQuotient` (`Geometry/Manifold/GroupAction/Quotient.lean`) | Tau Ceti |
| Coadjoint orbit $G/G_\nu$ with its symplectic form | `Module.Dual.coadjointOrbitForm` (`Geometry/Symplectic/Coadjoint/Orbit.lean`) | Tau Ceti |
| Smooth fibre bundle, principal bundle, associated bundle | `TauCeti.ContMDiffFiberBundle`, `TauCeti.PrincipalBundle`, `TauCeti.AssociatedBundle` | Tau Ceti |
| Fibration with an atlas of structure group $H$; symplectic fibration; forms restricting to the fibre forms | `TauCeti.MapFiber.Atlas` with `IsContMDiff`; structure groups `TauCeti.MapFiber.Atlas.HasStructureGroup`, symplectic atlases, `TauCeti.MapFiber.Atlas.RestrictsTo` (see *Fibrations, connections and diffeomorphism groups*) | Tau Ceti, *Symplectic fibrations* |
| Connection on a fibration, horizontal lift | `TauCeti.IsEhresmannConnection`, `horizontalLift` | Tau Ceti |
| Parallel transport, holonomy, curvature of a connection | `TauCeti.IsEhresmannConnection.parallelTransport`, `curvature` | *Parallel transport* |
| Connection 1-form on a principal bundle, its curvature | `SymplecticGeometry.IsConnectionForm`, `SymplecticGeometry.connectionCurvature` | *Principal connections* |
| Flux, flux group, endpoint flux | `TauCeti.Diffeotopy.flux`, `TauCeti.fluxGroup`, `TauCeti.endpointFlux` | Tau Ceti |
| Integration over the fibre | `TauCeti.MapFiber.Atlas.fiberIntegral` | *Integration over the fibre* |
| Diffeomorphism group with the $C^\infty$ topology | `TauCeti.Diff` with `Diffeomorph.weakWhitneyTopology` | Tau Ceti |

### Standard model: the definitions and their API

- `StdSpace ι := EuclideanSpace ℝ (ι ⊕ ι)`, an `abbrev`.
- Coordinates: `StdSpace.x, StdSpace.y : StdSpace ι →ₗ[ℝ] (ι → ℝ)`, with `ι`
  implicit so that `z.x` and `z.y` elaborate by dot notation, defined as
  `LinearMap.fst` and `LinearMap.snd` after `equivProd ι` (`x_def`, `y_def`, by `(rfl)`);
  they come with
  `@[simp]` lemmas `StdSpace.x_apply`, `StdSpace.y_apply`; `StdSpace.ext`
  (`z.x = w.x → z.y = w.y → z = w`, tagged `@[ext]`); the constructor
  `StdSpace.equivProd ι : StdSpace ι ≃ₗ[ℝ] (ι → ℝ) × (ι → ℝ)` (built from
  `EuclideanSpace.equiv` and `ContinuousLinearEquiv.sumPiEquivProdPi`, `equivProd_def`
  by `(rfl)`), with `@[simp]`
  lemmas for `x`, `y` of `(equivProd ι).symm (a, b)` and for
  `equivProd ι z = (z.x, z.y)`; and `x`, `y` of
  `complexToRealEuclidean ι u` as the real and imaginary parts of `u`.
- `stdForm ι : TauCeti.SymplecticForm (StdSpace ι)`, defined as
  `(stdComplexPiSymplecticForm ι).transport
  (complexToRealEuclidean ι).toLinearEquiv`, with
  `stdForm_def` (by `(rfl)`), `@[simp] stdForm_apply` in terms of `x` and `y`,
  `stdForm_toBilinForm` (the relation with `Matrix.toBilin' (Matrix.J ι ℝ)`),
  and `stdForm_apply_eq_inner`.
- `stdComplexStructure ι : TauCeti.AlmostComplexStructure (StdSpace ι)`,
  defined as the transport of `AlmostComplexStructure.ofComplexModule (ι → ℂ)`
  along the same map, with `stdComplexStructure_def`, `@[simp]` lemmas
  `stdComplexStructure_x` and `stdComplexStructure_y`,
  `stdComplexStructure_eq_toEuclideanLin_J`, and
  `stdForm_compatible : (stdForm ι).Compatible (stdComplexStructure ι)`, which
  is `stdComplexPiSymplecticForm_compatible.transport`.
- The comparison with Tau Ceti's product model: the symplectomorphism from
  `stdForm ι` to `stdSymplecticForm` on
  `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι` along
  `EuclideanSpace.sumEquivProd`, carrying `stdComplexStructure ι` to
  `AlmostComplexStructure.product`.
- Relabelling the coordinate pairs: `isSymplectomorphism_piLpCongrLeft_sumCongr`,
  for `σ : ι ≃ κ`, says that
  `(LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (σ.sumCongr σ)).toLinearEquiv` carries
  `stdForm ι` to `stdForm κ`.
- The direct sum of two models: `StdSpace.sumEquiv ι κ : StdSpace (ι ⊕ κ)
  ≃L[ℝ] StdSpace ι × StdSpace κ`, which regroups the coordinates by
  `Equiv.sumSumSumComm` as Tau Ceti's `Matrix.symplecticSum` does, with
  `@[simp]` lemmas for `x` and `y` of both components and the lemma that it
  carries `stdForm (ι ⊕ κ)` to `(stdForm ι).prod (stdForm κ)`, the product
  being Tau Ceti's `TauCeti.SymplecticForm.prod`;
  and, in `Matrix.lean`, that it conjugates
  `Matrix.toEuclideanLin (Matrix.symplecticSum A B)` to the product of the
  maps of `A` and `B`. *Symplectic vector bundles* writes frames of a direct
  sum with it, so that their transition loops are `TauCeti.GLSymplectic.sum`
  of two loops, the form `TauCeti.GLSymplectic.maslovIndex_sum` takes. It is
  built by *Lagrangian Grassmannian*'s issue on direct sums (#126), which came
  before that part's first issue on direct sums, not by *Standard model*'s
  issues.
- The complex coordinates: `StdSpace.complexEuclideanEquiv ι :
  EuclideanSpace ℂ ι ≃L[ℝ] StdSpace ι`, the composite of
  `PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℂ)` with
  `TauCeti.complexToRealEuclidean ι`, with `complexEuclideanEquiv_def` and the
  `@[simp]` lemmas `x_complexEuclideanEquiv` and `y_complexEuclideanEquiv`
  (the real and imaginary parts of each coordinate), and
  `stdComplexStructure_complexEuclideanEquiv` (it carries multiplication by
  `I` to `J₀`). *Lagrangian
  Grassmannian* uses it to compare its subspaces of `StdSpace ι` with Tau
  Ceti's subspaces of `EuclideanSpace ℂ ι`. It is built by that part's issue
  on Lagrangian frames (#118), not by *Standard model*'s issues.
- The matrix dictionary: `mem_symplecticGroup_iff_isSymplectomorphism`
  (`A ∈ Matrix.symplecticGroup ι ℝ` if and only if `Matrix.toEuclideanLin A`
  preserves `stdForm ι`), and `mem_GLSymplectic_iff_isSymplectomorphism`, its
  form for `g : GL (ι ⊕ ι) ℝ` in Tau Ceti's `GLSymplectic ι ℝ` and the
  automorphism `Matrix.toEuclideanCLE g`; a real matrix commutes with
  `Matrix.J` if and only if its map commutes with `stdComplexStructure ι`; and
  the complex side, from Tau Ceti's `Matrix.realify_I_smul_one` and
  `complexToRealEuclidean_mulVec` (`Analysis/Complex/Euclidean/Matrix.lean`):
  `complexToRealEuclidean` intertwines a complex matrix with its `Matrix.realify`.

## Parts

Each part lists its folder and files, what it builds on, and the milestones it
proves. Files are under `SymplecticGeometry/`. A part's files may be split
further when they grow, following `AGENTS.md`. The design is the plan, not
a list of what the library has: files and imports added beyond those it
names are not recorded, here or in a part's design file,
`design/<part>.md`, and the lists below and the notes in the build-order
table may fall behind.

### 1. Standard model

- **Files:** `LinearAlgebra/Symplectic/Standard/Basic.lean` (`StdSpace`, its
  coordinates, `stdForm`, `stdComplexStructure`, the product comparison,
  `isSymplectomorphism_piLpCongrLeft_sumCongr` with its coordinates
  `StdSpace.x_piLpCongrLeft_sumCongr` and `StdSpace.y_piLpCongrLeft_sumCongr`,
  `StdSpace.sumEquiv`, and the additions of *Lagrangian Grassmannian*:
  `StdSpace.complexEuclideanEquiv`, `StdSpace.swap`, `StdSpace.finSumIsometry`),
  `LinearAlgebra/Symplectic/Standard/Matrix.lean` (the matrix dictionary).
- **Builds on:** Mathlib, Tau Ceti. `Matrix.lean` also imports two general
  matrix files that *Siegel upper half space* lists:
  `LinearAlgebra/Matrix/Block.lean` (the block identities of a matrix with
  square $-1$) and `LinearAlgebra/Matrix/Symmetric.lean` (for
  `Matrix.isSymm_mul_nonsing_inv_of_transpose_mul_eq`). Both import only
  Mathlib and Tau Ceti and are merged, so the part still sits at level 0.
  It imports, too, `LinearAlgebra/Matrix/SymplecticGroup/Basic.lean` of
  *Symplectic group*, for `Matrix.neg_J_mul_eq_fromBlocks`; that file also
  imports only Mathlib and Tau Ceti and is merged, so the level stays 0.
  Likewise it imports `LinearAlgebra/Matrix/PosDef/Block.lean` of *Siegel
  upper half space*, for `Matrix.PosDef.toBlocks₁₁`; that file imports only
  Mathlib and Tau Ceti and is merged, so the level stays 0.
  `Matrix.lean` also imports `LinearAlgebra/Symplectic/Compatible.lean` of
  *Compatible complex structures*, for the matrix form of compatibility on
  `StdSpace ι` (`compatible_stdForm_iff_posDef` and its companions). That
  file imports only Tau Ceti, Mathlib, `Standard/Basic.lean`,
  `LinearAlgebra/ComplexStructure/Action.lean`,
  `Geometry/Symplectic/Darboux/EuclideanBasis.lean` of *Compatible complex
  structures* (which imports only Tau Ceti) and
  `LinearAlgebra/Symplectic/Subspace.lean`, none of which imports
  `Matrix.lean`, and it is merged; so there is no cycle, and the files that
  build on the dictionary see no change in order.
- **Milestones:** none. It is the interface the other parts share.

### 2. Symplectic vector spaces

- **Files:** `LinearAlgebra/Symplectic/Darboux.lean` (over any field `k`, the
  isometry of an alternating nondegenerate form on a space of dimension $2n$
  with `-stdSymplecticBilinForm k n` on `Fin n ⊕ Fin n → k`, from Tau Ceti's
  `LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J` and
  `Module.Basis.isometryEquivOfToMatrixEq`, with the basis reordered as in
  *Conventions*; its properties come from `isAlt_stdSymplecticBilinForm`,
  `stdSymplecticBilinForm_nondegenerate` and
  `stdSymplecticBilinForm_single_single` through negation; over $\mathbb{R}$
  the same with `stdForm`),
  `LinearAlgebra/Symplectic/Subspace.lean` (isotropic if and only if the
  complement is coisotropic; every isotropic subspace lies in a Lagrangian
  one), `LinearAlgebra/Symplectic/Reduction.lean` (for coisotropic $W$, the
  form on $W/W^\omega$ and its uniqueness, from Tau Ceti's `reduction`, whose
  quotient is by $W\cap W^\omega=W^\omega$).
- **Builds on:** *Standard model*, *Symplectic group* (its entry lemmas for
  `Matrix.J`).
- **Milestones:** *Linear Darboux theorem*, *Symplectic complements*,
  *Lagrangian extension lemma*, *Linear symplectic reduction*.

### 3. Symplectic group

- **Files:** `LinearAlgebra/Matrix/SymplecticGroup/Spectrum.lean` (eigenvalue
  pairing $\lambda\leftrightarrow\lambda^{-1}$ with algebraic multiplicities,
  even multiplicity at $\pm1$, $\omega_0$-orthogonality of eigenvectors for
  $\lambda\lambda'\neq1$ with the bilinear extension; from Tau Ceti's
  `SymplecticGroup.charpoly_inv`, `SymplecticGroup.reflect_charpolyRev` and
  `LinearMap.IsAdjointPair.apply_eq_zero_of_mem_genEigenspace`),
  `LinearAlgebra/Matrix/SymplecticGroup/Basic.lean` (algebraic facts beside
  Mathlib's `SymplecticGroup.transpose_mem`: the `simp` lemmas
  `Matrix.J_inl_inl`, `Matrix.J_inl_inr`, `Matrix.J_inr_inl` and
  `Matrix.J_inr_inr` for the four blocks of `Matrix.J`, over a commutative
  ring `Matrix.neg_J_mul_eq_fromBlocks` (the blocks of $-JM$ are those of
  $M$, the lower ones moved up and the upper ones negated and moved down) and
  `Matrix.IsSymm.mem_symplecticGroup_iff` (a symmetric $P$ is
  symplectic iff $(JP)^2=-1$), and, over a commutative star ring,
  `SymplecticGroup.star_mem` and `SymplecticGroup.star_mem_iff`),
  `Analysis/Matrix/Polar/Basic.lean` (the general right polar decomposition
  of `GL n 𝕜` over `RCLike 𝕜`, beside Tau Ceti's left forms:
  `Matrix.GeneralLinearGroup.posDef_sqrt_star_mul` and
  `Matrix.GeneralLinearGroup.existsUnique_unitary_mul_posDef`, and the
  unitary factor as $A(A^*A)^{-1/2}$,
  `Matrix.GeneralLinearGroup.coe_polarUnitary_eq_mul_rpow`),
  `Analysis/Matrix/Polar/Deformation.lean` (beside Tau Ceti's file of that
  name: its polar deformation at time $t$ is $A(A^*A)^{-t/2}$,
  `Matrix.GeneralLinearGroup.coe_polarDeformation_eq_mul_rpow`),
  `Analysis/Matrix/Polar/Symplectic.lean` (the right decomposition
  $\Psi=UP$ with uniqueness, `SymplecticGroup.existsUnique_unitary_mul_posDef`:
  Tau Ceti's `Units.polarUnitary_mul_sqrt_star_mul` gives the factorization,
  `Matrix.GeneralLinearGroup.existsUnique_unitary_mul_posDef` its uniqueness,
  and `SymplecticGroup.polarUnitary_mem` makes $U$ symplectic; what this file
  adds for the symplectic group is `SymplecticGroup.sqrt_star_mul_mem`, that
  $\sqrt{\Psi^*\Psi}$ is symplectic, $\Psi^*$ the conjugate transpose, which
  is `SymplecticGroup.sqrt_mul_star_mem` applied to `star Ψ`, symplectic by
  `SymplecticGroup.star_mem`; and the characterization of both factors,
  `SymplecticGroup.unitary_mul_posDef_eq_iff`, that they are
  $\Psi(\Psi^*\Psi)^{-1/2}$ and $(\Psi^*\Psi)^{1/2}$),
  `Analysis/Matrix/Polar/GLSymplectic.lean` (the deformation retraction:
  `TauCeti.GLSymplectic.polarHomotopy` fixes $\mathrm{U}(n)$ at all times,
  since it is the restriction of `Matrix.GeneralLinearGroup.polarHomotopy`
  (`Analysis/Matrix/Polar/Deformation.lean`), a homotopy relative to the
  unitary elements of $\mathrm{GL}(2n,\mathbb{R})$, that is, to $\mathrm{O}(2n)$, and
  $\mathrm{U}(n)=\mathrm{Sp}(2n)\cap\mathrm{O}(2n)$; at time $t$ it is `polarDeformation`, $P^{1-t}U$ for
  $\Psi=PU$, which a short computation identifies with the book's
  $f_t(\Psi)=\Psi(\Psi^T\Psi)^{-t/2}$; so it is a homotopy rel $\mathrm{U}(n)$ from the
  identity to the retraction, and the inclusion
  $\mathrm{U}(n)\to\mathrm{Sp}(2n)$ is a `ContinuousMap.HomotopyEquiv`, by
  Tau Ceti's `ContinuousMap.HomotopyEquiv.ofDeformationRetraction`).
- **Builds on:** Mathlib, Tau Ceti.
- **Milestones:** *Spectrum of a symplectic matrix*, *Symplectic polar
  decomposition and the maximal compact subgroup*.

### 4. Unitary group topology

- **Files:** first a general file, named like the Tau Ceti file it
  extends so that the two merge upstream. That the homotopy groups of the
  space of unit vectors `finiteOrthonormalFrame 𝕜 1 N` vanish below degree
  $\dim_{\mathbb{R}}\mathbb{k}^N-1$, over any `RCLike 𝕜`, is Tau Ceti's
  `TauCeti.finiteOrthonormalFrame.subsingleton_homotopyGroup` with $r=1$
  (`Topology/Grassmannian/StiefelFibration/ForgetLast.lean`).
  `Topology/Grassmannian/StiefelFibration/Stability.lean`:
  the stable range `Matrix.UnitaryGroup.isNConnected_fromBlocksOne`, in the
  namespace of Tau Ceti's `fromBlocksOne`, `detCircle` and
  `instPathConnectedSpace` for Mathlib's `Matrix.unitaryGroup`. It is stated
  over any `RCLike 𝕜`, with the hypothesis
  `2 ≤ Module.finrank ℝ 𝕜 * (m + 1)`: the block inclusion `fromBlocksOne` of
  $\mathrm{U}(m,\mathbb{k})$ in $\mathrm{U}(1+m,\mathbb{k})$ is
  `Module.finrank ℝ 𝕜 * (m + 1) - 2`-connected. For $\mathbb{k}=\mathbb{C}$
  the hypothesis always holds and the bound is $2m$, the case the milestone
  uses; for $\mathbb{k}=\mathbb{R}$ it gives $\mathrm{O}(m)\to\mathrm{O}(1+m)$
  for $m\ge1$. The hypothesis is needed: for $\mathbb{k}=\mathbb{R}$ and
  $m=0$ the bound truncates to $0$ in `ℕ`, and $\mathrm{O}(0)\to\mathrm{O}(1)=\{\pm1\}$
  does not reach $-1$. It is the analogue of
  `TauCeti.Matrix.SpecialOrthogonalGroup.isNConnected_fromBlocksOne` and is
  proved in the same way. Then
  `Analysis/Matrix/UnitaryGroup/FundamentalGroup.lean`, which holds the
  milestone and `Matrix.UnitaryGroup.homotopic_iff_angleChange_eq` (paths in
  $\mathrm{U}(n)$ with the same ends are homotopic iff $\det$ has the same
  `Circle.angleChange` along them, for every $n$): $\det:\mathrm{U}(n)\to S^1$,
  Tau Ceti's
  `Matrix.UnitaryGroup.detCircle`, induces an isomorphism of fundamental
  groups for $n\ge1$, by induction from $\mathrm{U}(1)\cong S^1$, which is
  Tau Ceti's `Matrix.UnitaryGroup.detCircleEquivOfUnique`
  (`Analysis/Matrix/UnitaryGroup/Torus.lean`, with forward map `detCircle`),
  along the
  stable range, which commutes with $\det$; and its corollary that
  $\mathrm{SU}(n)$ (Mathlib's `Matrix.specialUnitaryGroup`) is simply
  connected, for $n\ge1$ through the continuous retraction
  `Matrix.UnitaryGroup.toSpecialUnitaryAt` of Tau Ceti, of $\mathrm{U}(n)$
  onto $\mathrm{SU}(n)$, $A\mapsto A\operatorname{diag}(1,\dots,\overline{\det A},\dots,1)$
  with the correcting entry at a chosen index $i_0$: a loop
  in $\mathrm{SU}(n)$ is trivial in $\pi_1(\mathrm{U}(n))$, since its
  determinant is constant, and the retraction carries the null-homotopy back.
  For $n=0$ the group is a point. The two counterexamples for $n=0$, for
  $\mathrm{U}(0)$ and $\mathrm{Sp}(0)$, both apply the general
  `FundamentalGroup.not_surjective_map_circle_of_subsingleton`
  (`AlgebraicTopology/FundamentalGroup.lean`), which also holds
  `Circle.homotopic_iff_angleChange_map_eq`: for `d : X → S¹` injective on
  $\pi_1$, two paths with the same ends are homotopic iff their images have
  the same angle change. The retraction and the facts about `detCircle`
  it uses are in `Analysis/Matrix/UnitaryGroup/Basic.lean`.
  Tau Ceti's `Matrix.instSimplyConnectedSpaceSpecialUnitaryGroupFinTwoComplex`
  is the case $n=2$. Last, `Analysis/Matrix/SymplecticGroup/FundamentalGroup.lean`
  ($\pi_1(\mathrm{Sp}(2n))\cong\mathbb{Z}$ for $n\ge1$, through *Symplectic
  group*'s homotopy equivalence).
- **Builds on:** Mathlib, Tau Ceti; the last file also on *Symplectic group*.
  The stable range uses Tau Ceti's unitary Stiefel fibration over `RCLike 𝕜`
  with $r=1$: `TauCeti.unitaryFrameMap` ($\mathrm{U}(1+m,\mathbb{k})\to$ unit
  vectors of $\mathbb{k}^{1+m}$) is a Serre fibration
  (`TauCeti.unitaryFrameMap_mem_serreFibrations`,
  `exists_trivialization_unitaryFrameMap`,
  `Topology/Grassmannian/StiefelFibration/Unitary.lean`) whose fibre is the
  block-embedded $\mathrm{U}(m,\mathbb{k})$
  (`TauCeti.unitaryFrameFiberHomeomorph`); the base is a sphere of
  dimension `Module.finrank ℝ 𝕜 * (m + 1) - 1` (for $\mathbb{C}$,
  $S^{2m+1}$), so the fibre inclusion is connected one degree below that, by
  `TauCeti.TopCat.isNConnected_fiberι_of_mem_serreFibrations`, which needs a
  path-connected base: the sphere has positive dimension exactly under the
  hypothesis `2 ≤ Module.finrank ℝ 𝕜 * (m + 1)`. Only $r=1$ is
  planned: a general $r$ would need the fibration of frames by `forgetLast`
  over $\mathbb{C}$, which Tau Ceti has only over $\mathbb{R}$, and nothing
  here needs it. Connectedness of $\mathrm{U}(n)$ is Tau Ceti's
  `Matrix.UnitaryGroup.instPathConnectedSpace`, and $\pi_1(S^1)$ is
  `Circle.fundamentalGroupMulEquiv`.
- **Milestones:** *Fundamental group of the unitary group*: the isomorphisms
  for $n\ge1$, and the simple connectivity of $\mathrm{SU}(n)$ for every $n$.
  For $n=0$ both $\mathrm{U}(0)$ and $\mathrm{Sp}(0)$ are trivial groups, while
  $\pi_1(S^1)\cong\mathbb{Z}$. `ERRATA.md` records this, and the part proves
  next to each isomorphism that the group is trivial for $n=0$.

### 5. Maslov index (needs `design/maslov-index.md`)

One part for all Maslov indices, because they share their framework (loops,
free homotopies, the axioms, the uniqueness argument). Its design file splits
it into issues; the overview fixes its folders and its dependencies.

- **Files:** `Analysis/Matrix/SymplecticGroup/Maslov.lean` (symplectic
  loops: the converse of the homotopy axiom from part 4, uniqueness of the
  axiomatic characterization; named like Tau Ceti's file of the same subject,
  so that the two merge upstream), `LinearAlgebra/Symplectic/Lagrangian/Maslov/`
  (loops and paths of Lagrangian subspaces of `StdSpace ι`). Outside these
  folders, two files about Tau Ceti's `GLSymplectic` itself, which the
  uniqueness statement needs, placed where Tau Ceti keeps the algebra and the
  topology of that group so that they can move there unchanged:
  `LinearAlgebra/Matrix/GeneralLinearGroup/Symplectic/Reindex.lean`
  (`TauCeti.GLSymplectic.reindex` along `ι ≃ κ`, with its API) and
  `Topology/Algebra/SymplecticGroup.lean` (its continuity,
  `continuous_reindex`). The proof that reindexing keeps $\rho$ adds three
  lemmas where their subjects live: `Matrix.realify_submatrix`
  (`LinearAlgebra/Matrix/Realify.lean`) and
  `Matrix.GeneralLinearGroup.coe_polarUnitary_reindex`
  (`Analysis/Matrix/Polar/Basic.lean`) with its symplectic form
  `TauCeti.GLSymplectic.coe_polarUnitary_reindex`
  (`Analysis/Matrix/Polar/GLSymplectic.lean`); and `Path.Homotopic.homotopicWith`
  (`Topology/Homotopy/Path.lean`) says that a homotopy of loops with fixed
  ends is a free one. The crossing forms add a third file outside these
  folders, `Analysis/Calculus/Deriv/Matrix.lean` (derivatives of
  matrix-valued functions), beside Tau Ceti's file of the same name so that
  the two merge upstream. The regular pieces add a fourth,
  `Data/Matrix/Basis.lean` (the matrix `1 + Eᵢᵢ a`, beside the files of the
  same name in Mathlib and Tau Ceti).
- **Builds on:** *Standard model*, *Symplectic group*, *Unitary group
  topology*, *Lagrangian Grassmannian*. From Mathlib and Tau Ceti, in two
  ways, none of it re-derived:
  - *Used as they are*, on matrices: the symplectic loop index
    `TauCeti.GLSymplectic.maslovIndex` on loops in `GLSymplectic n ℝ`, with
    the axioms Tau Ceti proves for it, which the part extends; for the
    reindexing of `GL (ι ⊕ ι) R`, Mathlib's
    `Matrix.GeneralLinearGroup.reindex` and Tau Ceti's
    `Matrix.reindex_sumCongr_J`.
  - *Transferred to `StdSpace ι` by choosing unitary frames* (read along
    `complexToRealEuclidean`), for the Lagrangian theory only: the
    Lagrangian loop index through `realImageLoop`,
    `maslovIndex_realImageLoop`, `maslovPhase_realImage` and
    `Matrix.UnitaryGroup.maslovIndex_eq_degree` (the book's $\det(U^2)$
    description), compared with Tau Ceti's loop index
    `TotallyRealLoop.maslovIndex` (`LinearAlgebra/TotallyReal/Maslov/`) by a
    theorem, while its direct-sum axiom, half-turns and angle description
    come from Tau Ceti's Souriau map and degree lemmas; the
    path index from Souriau's formula `Matrix.UnitaryGroup.maslovIndex` and
    the Souriau map `Matrix.UnitaryGroup.souriau`
    (`Analysis/Matrix/UnitaryGroup/Maslov.lean`), which is defined for
    every path, while `TotallyRealPath.transverseMaslovIndex`
    (`LinearAlgebra/TotallyReal/Maslov/Transverse.lean`), defined only for
    paths with ends transverse to $\mathbb{R}^n$, enters as the special
    case that a theorem identifies; and the crossing-form theorems of
    `Analysis/Matrix/UnitaryGroup/Maslov/` and
    `Analysis/Matrix/HermitianSignature/`, applied to frames.
- **Milestones:** *Maslov index for loops of symplectic matrices*, *Maslov
  index for loops of Lagrangian subspaces*, *Crossing-form formula for the
  Maslov index*, *Maslov index for paths of Lagrangian subspaces*.
- **The design file decides:** how "a function on loops for every $n$" is
  stated for uniqueness (a family indexed by `n : ℕ` on `Fin n`, with the
  direct-sum axiom through `Fin (n + m) ≃ Fin n ⊕ Fin m`); whether the path
  index is real- or $\tfrac12\mathbb{Z}$-valued (Tau Ceti's is real); how a
  general reference Lagrangian $V$ reduces to $\mathbb{R}^n\times\{0\}$ by
  $\mathrm{Sp}(2n)$-transitivity (from *Lagrangian Grassmannian*); the
  dictionary between Lagrangian subspaces of `StdSpace ι` and Tau Ceti's
  totally real subspaces of `ι → ℂ`; and the order of the issues, symplectic
  loops first, since they need only parts 3 and 4.

### 6. Lagrangian Grassmannian (needs `design/lagrangian-grassmannian.md`)

- **Files:** `LinearAlgebra/Symplectic/Lagrangian/Basic.lean` (the type
  $\mathcal{L}(V,\omega)$ of Lagrangian subspaces, with its `SetLike` and
  `ext` API, and, for any $(V,\omega)$ of finite dimension, that two
  Lagrangians are complementary if and only if they meet in $0$),
  `LinearAlgebra/Symplectic/Lagrangian/Frame.lean` (the frame
  criterion $\operatorname{rank}=n$, $X^TY=Y^TX$; graphs of symmetric
  matrices, from Tau Ceti's `isLagrangian_graph_iff_of_pairing`),
  `LinearAlgebra/Symplectic/Lagrangian/Action.lean` (the action of
  $\mathrm{Sp}(2n)$, transitivity already for $\mathrm{U}(n)$ and the
  stabilizer $\mathrm{O}(n)$, hence
  $\mathcal{L}(n)\simeq\mathrm{U}(n)/\mathrm{O}(n)$ as sets by
  orbit–stabilizer),
  `LinearAlgebra/Symplectic/Lagrangian/Transverse.lean` (the chart points
  and transverse Lagrangians: any two have a common transverse Lagrangian,
  and $\mathrm{Sp}(2n)$ acts transitively on transverse pairs),
  `LinearAlgebra/Symplectic/Lagrangian/Sum.lean` (the direct sum of
  Lagrangians and the reindexing equivalence, their compatibility with
  unitary frames, and the equivariance of the sum),
  `LinearAlgebra/TotallyReal/Euclidean.lean` (the range of Tau Ceti's
  `Matrix.lagrangianChart`, beside Tau Ceti's file of that name),
  `Topology/Grassmannian/Lagrangian/Basic.lean` (the topology of
  $\mathcal{L}(V,\omega)$), `Topology/Grassmannian/Lagrangian/Quotient.lean`
  (continuity of the action, and the equivalence
  $\mathcal{L}(n)\simeq\mathrm{U}(n)/\mathrm{O}(n)$ of `Action.lean` as a
  homeomorphism), `Topology/Grassmannian/Lagrangian/Finite.lean` (for
  `ι = Fin n`, the embedding of $\mathcal{L}(n)$ into Tau Ceti's
  `TauCeti.finiteGrassmannian ℝ n (n + n)`, with its range),
  `Topology/Grassmannian/Lagrangian/Graph.lean` (the graph
  charts by symmetric matrices),
  `Geometry/Manifold/Instances/LagrangianGrassmannian.lean` (the manifold
  structure of dimension $n(n+1)/2$, from the charts of `Graph.lean`),
  `Topology/Grassmannian/Lagrangian/Fibration.lean` (path lifting),
  `Topology/Grassmannian/Lagrangian/Sum.lean` (continuity of the direct sum,
  and the reindexing equivalence as a homeomorphism).
  Three files of general matrix theory, outside the part's folders, serve
  it: `LinearAlgebra/Matrix/UnitaryGroup/Real.lean`
  (`Matrix.UnitaryGroup.realSubgroup`, the real points
  $\mathrm{O}(n)\subset\mathrm{U}(n)$ as a subgroup of
  `Matrix.unitaryGroup ι ℂ`: Tau Ceti's subgroup of `GL ι ℂ` from
  `TauCeti.GLOrthogonal.inf_unitarySubgroup_eq_map_real`, carried along
  Mathlib's `unitarySubgroupUnitsEquiv`; it is the stabilizer of $V_0$ and
  the fibre of `Fibration.lean`), `LinearAlgebra/Matrix/OfReal.lean` (for
  real $X,Y$, the complex frame $X+iY$: its Gram matrix is real when
  $X^TY=Y^TX$, and its real image is the range of
  `Matrix.toEuclideanLin (Matrix.fromRows X Y)`), and
  `LinearAlgebra/Matrix/SelfAdjoint.lean` (`Matrix.finrank_selfAdjoint`:
  the symmetric $n\times n$ matrices have dimension $n(n+1)/2$, from Tau
  Ceti's `LinearMap.BilinForm.finrank_symmSubmodule`). More general
  files serve it too:
  `Analysis/InnerProductSpace/PiL2.lean`
  (`Matrix.piLpCongrLeft_toEuclideanLin_apply`: relabelling coordinates
  along `e` turns the action of `M` into that of `reindex e e M`),
  `Analysis/Matrix/EuclideanLin.lean`
  (`Matrix.coe_toLinearEquiv_toEuclideanCLE`: the linear equivalence of an
  invertible matrix `A` is `Matrix.toEuclideanLin A` as a linear map),
  `Analysis/Normed/Lp/PiLp.lean`
  (`LinearIsometryEquiv.piLpCongrLeft_trans`: relabelling along `e`, then
  along `f`, is relabelling along `e.trans f`). Two files under
  `Topology/` serve it as well: `Topology/Algebra/Matrix/Realify.lean`
  (`TauCeti.GLSymplectic.sum_ofUnitary`: `ofUnitary` turns the block sum
  `Matrix.UnitaryGroup.sum` into `GLSymplectic.sum`; it sits beside the
  Tau Ceti file of that name, which defines `ofUnitary`), and
  `Topology/Grassmannian/Tautological.lean`
  (`TauCeti.finiteGrassmannian.isClosedEmbedding_starProjection_toEuclidean`,
  for any `RCLike 𝕜`: on the compact space `finiteGrassmannian 𝕜 r N`, the
  map to orthogonal projections is a closed embedding; `Finite.lean` uses
  it). The part also adds declarations about `StdSpace ι` alone to
  *Standard model*'s `Standard/Basic.lean`: `StdSpace.complexEuclideanEquiv`,
  the map from `EuclideanSpace ℂ ι`; the coordinate swap `StdSpace.swap`;
  the isometry `StdSpace.finSumIsometry` onto `EuclideanSpace ℝ (Fin (n + n))`;
  and the coordinates `StdSpace.x_piLpCongrLeft_sumCongr` and
  `StdSpace.y_piLpCongrLeft_sumCongr` of the coordinate permutation; the
  part's design lists them with their API. For the coordinate permutation
  along `Equiv.sumCongr e e` it uses the existing
  `isSymplectomorphism_piLpCongrLeft_sumCongr` of §1.
  The `LinearAlgebra/` files import no `Topology/` file of this part; the
  general `Topology/Algebra/Matrix/Realify.lean`, which
  `LinearAlgebra/Symplectic/Lagrangian/Sum.lean` imports, is not one of
  them. Below,
  $V_0$ is $\mathbb{R}^n\times\{0\}$ ($y=0$), $V_1$ is
  $\{0\}\times\mathbb{R}^n$ ($x=0$), and the unitary frame map
  $\mathrm{U}(n)\to\mathcal{L}(n)$ sends $U$ to the image of $V_0$ under
  `Matrix.toEuclideanLin (Matrix.realify U)`. `design/maslov-index.md` lists
  what the *Maslov index* part needs of the items below.
- **Builds on:** *Standard model*, including `StdSpace.sumEquiv` for the
  direct sum; *Symplectic vector spaces*, only `Subspace.lean`, for
  `TauCeti.SymplecticForm.isLagrangian_iff_isIsotropic_and_two_mul_finrank_eq`
  in the frame criterion. From Tau Ceti, transferred along `complexToRealEuclidean`: the
  chart `Matrix.lagrangianChart` (`LinearAlgebra/TotallyReal/Euclidean.lean`);
  frames and the stabilizer through `Matrix.realImage`,
  `Matrix.exists_mem_orthogonalGroup_eq_mul_map_ofReal` and
  `realOrthonormalize_mem_unitaryGroup`. $\mathrm{Sp}$-transitivity does not
  come from Witt's theorem: $\mathrm{U}(n)$ already acts transitively
  (`Action.lean`), through `TauCeti.GLSymplectic.ofUnitary`, so the
  $\mathrm{Sp}(2n)$-orbit of $V_0$ is all of $\mathcal{L}(n)$.
- **Graphs of transverse Lagrangians** (`Frame.lean`). A Lagrangian
  transverse to $V_1$ is $\{y=Sx\}$, and one transverse to $V_0$ is
  $\{x=Sy\}$, for a unique symmetric $S$. This is the converse of the graph
  criterion: Mathlib's `Submodule.exists_eq_graph` gives a linear map whose
  `LinearMap.graph` is the subspace, from the bijectivity of the projection
  onto the complement, and Tau Ceti's `isLagrangian_graph_iff_of_pairing`
  its symmetry; uniqueness is that of a graph.
- **The range of `Matrix.lagrangianChart`**
  (`LinearAlgebra/TotallyReal/Euclidean.lean`, namespace `Matrix`). The
  surjectivity Tau Ceti lacks beside `Matrix.lagrangianChart_injective` and
  `Matrix.lagrangianChart_inf_realSubspace`, in Tau Ceti's terms: a real
  subspace `V` of `EuclideanSpace ℂ n` that is `IsMaximalTotallyReal` for
  multiplication by $i$, is isotropic in the form of
  `Matrix.im_inner_eq_zero_of_mem_lagrangianChart`
  (`(inner ℂ v w).im = 0` for `v w ∈ V`), and has
  `V ⊓ TauCeti.realSubspace n = ⊥` is `lagrangianChart S` for a symmetric
  `S`. The isotropy cannot be dropped: for `n = Fin 2` and
  $S=\begin{pmatrix}0&1\\0&0\end{pmatrix}$, $\det(S+i)=-1$, so
  `lagrangianChart S` is maximal totally real and transverse to
  `realSubspace (Fin 2)`, but by `Matrix.lagrangianChart_injective` it is
  the chart of no symmetric matrix. The statement follows from the second
  graph statement, transferred along `StdSpace.complexEuclideanEquiv n`,
  which carries `TauCeti.realSubspace n` to $V_0$ and
  `lagrangianChart S` to $\{x=Sy\}$.
- **Graph charts** (`Graph.lean`). For the projection topology (**The
  topology** below),
  the Lagrangians transverse to $V_0$, and those transverse to $V_1$, form
  open subsets of $\mathcal{L}(n)$, each homeomorphic to the symmetric
  matrices by the graph statements above; the first chart sends $S$ to the
  transfer of `Matrix.lagrangianChart S`. Tau Ceti's
  `Topology/Grassmannian/Graph.lean` does the same for
  `TauCeti.finiteGrassmannian`. The manifold file and `Fibration.lean` both
  use these charts, so that no `Topology/` file depends on the manifold one.
- **Path lifting** (`Fibration.lean`). The unitary frame map is locally
  trivial with fibre $\mathrm{O}(n)$, hence a Serre fibration, so every path
  in $\mathcal{L}(n)$ lifts to a path in $\mathrm{U}(n)$ from any frame of its
  start point. Its fibres are the left cosets of the real orthogonal matrices
  (from `Action.lean`). Near $V_1$, a continuous section sends $\{x=Sy\}$ to
  the unitary matrix `unitaryOfFrame` (`Action.lean`) of the Lagrangian
  frame `fromRows S 1`, $S$ being the coordinate of the graph chart of
  `Graph.lean` on the Lagrangians transverse to $V_0$: it frames
  $\{x=Sy\}$ by `graphY_eq_unitaryFrame` and is continuous by
  `continuous_unitaryOfFrame`, so no unitary frame is built by hand; left
  translation by $\mathrm{U}(n)$ gives sections near every point. Tau Ceti's
  `Subgroup.localSectionTrivializationOfCosetFibers`
  (`Topology/Algebra/Group/Quotient/LocalSection.lean`) turns these sections
  into trivializations,
  `TauCeti.TopCat.mem_serreFibrations_of_exists_trivialization`
  (`Topology/Homotopy/SerreFibration/FiberBundle.lean`) into a Serre
  fibration, and `TauCeti.TopCat.exists_path_lift_of_mem_serreFibrations`
  (`Topology/Homotopy/SerreFibration/Basic.lean`) into the lift. Tau Ceti's
  unitary Stiefel fibration (`Topology/Grassmannian/StiefelFibration/Unitary.lean`)
  is built the same way and is the model for the file.
- **Direct sums and reindexing** (`LinearAlgebra/Symplectic/Lagrangian/Sum.lean`
  and `Topology/Grassmannian/Lagrangian/Sum.lean`). In the `LinearAlgebra/`
  file: the direct sum
  $\mathcal{L}(\iota)\times\mathcal{L}(\kappa)\to\mathcal{L}(\iota\oplus\kappa)$,
  read in the coordinates of `Equiv.sumSumSumComm` as Tau Ceti's
  `Matrix.symplecticSum` is; and for `e : ι ≃ κ` the equivalence
  $\mathcal{L}(\iota)\simeq\mathcal{L}(\kappa)$, the image under the
  coordinate permutation along `Equiv.sumCongr e e`, with lemmas for its
  inverse and for composition. Both commute with unitary frames: the
  sum of the frames of $U$ and $U'$ is the frame of
  `Matrix.UnitaryGroup.sum (U, U')` (`LinearAlgebra/Matrix/UnitaryGroup/Block.lean`,
  through `Matrix.realify_fromBlocks_zero`), and reindexing the frame of $U$
  gives the frame of the reindexed matrix `U.submatrix e.symm e.symm`, unitary
  by Mathlib's `Matrix.submatrix_equiv_mem_unitary`. The sum is equivariant
  for `TauCeti.GLSymplectic.sum`
  (`LinearAlgebra/Matrix/GeneralLinearGroup/Symplectic/Sum.lean`). In the
  `Topology/` file: the sum is continuous, and the reindexing equivalence is
  a homeomorphism $\mathcal{L}(\iota)\simeq_t\mathcal{L}(\kappa)$. Continuity
  comes from $\mathcal{L}(n)\cong\mathrm{U}(n)/\mathrm{O}(n)$ (`Quotient.lean`):
  the frame map is an open quotient map, and so is a product of two such
  maps (Mathlib's `IsOpenQuotientMap.prodMap`). How the reindexing meets
  `GLSymplectic.reindex` is proved with that definition, in the *Maslov
  index* part, so that this part does not depend on it.
- **Transverse Lagrangians** (`Transverse.lean`). Any two Lagrangians
  $\Lambda_1,\Lambda_2$ have a common transverse Lagrangian: move $\Lambda_1$
  to $V_0$ by a unitary matrix; if $X+iY$ is a unitary frame of the moved
  $\Lambda_2$, then $\det(X+tY)$ is a polynomial in $t$ that is nonzero at
  $t=i$, so it has finitely many real roots, and for any other real $t$ the
  Lagrangian $\{x=-ty\}$, the transfer of `Matrix.lagrangianChart` of the
  scalar matrix $-t$ (Tau Ceti's `Matrix.lagrangianChart_smul_one` describes
  it), is transverse to both. And $\mathrm{Sp}(2n)$ acts
  transitively on pairs $(V,W)$ of transverse Lagrangians, each pair being
  $g\cdot(V_0,V_1)$: a unitary matrix takes $V$ to $V_0$; the moved $W$ is
  $\{x=Sy\}$ with $S$ symmetric, by the graph statement above; and the shear
  $\begin{pmatrix}1&S\\0&1\end{pmatrix}$ fixes $V_0$ and takes $V_1$ to
  $\{x=Sy\}$. The shear is symplectic for symmetric $S$ by Tau Ceti's
  `SymplecticGroup.fromBlocks_upper_mem`, for any index type, lifted to
  `TauCeti.GLSymplectic ι ℝ` by
  `(TauCeti.GLSymplectic.mulEquivSymplecticGroup ι ℝ).symm`. For $n=0$ these
  statements hold trivially, $\mathcal{L}(0)$ being a point.
- **Milestones:** *Lagrangian frames and the Lagrangian Grassmannian*.
- **The topology**, as the design file decides it: for $V$ a real inner
  product space of finite dimension, $\mathcal{L}(V,\omega)$ has the
  topology induced by orthogonal projections. The two other
  descriptions are theorems about it: the quotient
  $\mathrm{U}(n)/\mathrm{O}(n)$ in `Quotient.lean`, which the Maslov part
  uses, and the subspace topology of `TauCeti.finiteGrassmannian` in
  `Finite.lean`.

### 7. Linear nonsqueezing (needs `design/linear-nonsqueezing.md`)

- **Files:** `Analysis/InnerProductSpace/Symplectic/AffineSymplectic.lean`
  (affine symplectic maps $z\mapsto\Psi z+z_0$, symplectic balls and
  cylinders in `StdSpace ι`), `.../Nonsqueezing.lean` (affine nonsqueezing),
  `.../Ellipsoid.lean` (ellipsoids, their normal form $E(r)$, uniqueness of
  the symplectic spectrum, the volume formula; from Tau Ceti's Williamson
  theorem `TauCeti.SymplecticForm.exists_isDarbouxBasis_eq_sum_smul_elliptic_of_posDef`,
  with the book's radii $r_k^2=2/\nu_k$), `.../LinearWidth.lean` (the linear
  symplectic width and its value on ellipsoids), `.../Rigidity.lean` (the
  linear nonsqueezing property and linear rigidity).
- **Builds on:** *Standard model*.
- **Milestones:** *Affine nonsqueezing theorem*, *Simultaneous normal form of
  a symplectic form and an inner product*, *Linear symplectic width of an
  ellipsoid*, *Linear symplectic rigidity*.
- **The design file decides:** the value type of the width (`ℝ≥0∞`, so that
  unbounded sets have width $\infty$), how an ellipsoid centred at $0$ is
  given (a positive definite form, or the image of the unit ball under a
  linear isomorphism), and the statement of "symplectic or anti-symplectic".

### 8. Linear complex structures (needs `design/linear-complex-structures.md`)

- **Files:** as `design/linear-complex-structures.md` lists them.
  `LinearAlgebra/ComplexStructure/Action.lean` (the action of `V ≃ₗ[ℝ] V` on
  `AlmostComplexStructure V` by transport, and of `GL n ℝ` and
  `specialOrthogonalGroup n ℝ` on the structures of `EuclideanSpace ℝ n`),
  `Topology/ComplexStructure/Basic.lean` (closed embedding into operators,
  `T2Space`, `LocallyCompactSpace`, the homeomorphism with matrices of square
  $-1$, continuity of the actions),
  `LinearAlgebra/ComplexStructure/Standard.lean` (every complex structure $J$
  on a space of dimension $2\,|\iota|$ is the transport of
  `stdComplexStructure ι` by a linear isomorphism $\Phi$, which Tau Ceti's
  `TauCeti.AlmostComplexStructure.exists_linearEquiv_I_smul`
  (`Geometry/Symplectic/Finrank.lean`) gives from `ι → ℂ`, composed with
  `complexToRealEuclidean ι`; transitivity, the stabilizer of $J_0$ as the
  realified $\mathrm{GL}(n,\mathbb{C})$ by Tau Ceti's
  `Matrix.GeneralLinearGroup.mem_range_realify_iff`, positively oriented
  structures; an invertible symplectic matrix preserves and reflects
  compatibility with $\omega_0$, and `Matrix.symplecticGroup ι ℝ` acts
  transitively on the structures compatible with $\omega_0$ by conjugation),
  `Topology/Algebra/GroupAction/Transitive.lean` (the
  orbit–stabilizer homeomorphism for σ-compact groups),
  `Topology/ComplexStructure/Orbit.lean` (the space as the quotient
  $\mathrm{GL}(2n,\mathbb{R})/\mathrm{GL}(n,\mathbb{C})$; the positively
  oriented structures are clopen),
  `Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Polar.lean` (for a
  unit of square $-1$, the polar unitary factor conjugates the powers of the
  positive factor to their inverses), `Analysis/Matrix/Polar/Deformation.lean`
  (the polar deformation keeps square $-1$),
  `Topology/ComplexStructure/Orthogonal.lean` (the orthogonal complex
  structures and the deformation retraction onto them),
  `Topology/ComplexStructure/Oriented.lean` (the stabilizer of $J_0$ in
  $\mathrm{SO}(2n)$, the component of $J_0$, the two components for $n\ge1$,
  the homotopy type $\mathrm{SO}(2n)/\mathrm{U}(n)$, the case $\mathbb{R}^4$,
  homotopy equivalent to $S^2$, and the milestone).
- **Builds on:** *Standard model*; `Standard.lean` also imports the merged
  file `LinearAlgebra/Symplectic/Compatible.lean` of *Compatible complex
  structures*. Besides Mathlib and Tau Ceti, that file imports only
  `ComplexStructure/Action.lean` of this part, the
  `Geometry/Symplectic/Darboux/EuclideanBasis.lean` of *Compatible complex
  structures* (which imports only Tau Ceti), `Symplectic/Standard/Basic.lean` of *Standard model* and
  `Symplectic/Subspace.lean` of *Symplectic vector spaces*, all merged. In
  turn, *Compatible complex structures* uses the merged `Action.lean`,
  `Topology/ComplexStructure/Basic.lean`, `Standard.lean` and
  `Topology/ComplexStructure/Orthogonal.lean` of this part, so
  each of the two parts uses merged files of the other.
- **Milestones:** *Linear complex structures are standard*.
- **The design file decides:** how the quotient homeomorphism is obtained (an
  open orbit map, from a local section or from the inverse function theorem on
  `GL`); the models of $\mathrm{GL}(2n,\mathbb{R})/\mathrm{GL}(n,\mathbb{C})$
  and $\mathrm{SO}(2n)/\mathrm{U}(n)$ (Mathlib quotients by subgroups, or a
  space of complex structures compatible with the Euclidean metric); the
  model of $S^2$ and the explicit map for $n=2$; and the issues, a few hundred
  lines each, in that order.

### 9. Compatible complex structures (needs `design/compatible-complex-structures.md`)

- **Files:** `LinearAlgebra/Symplectic/Compatible.lean` (the four equivalent
  characterizations and the two of the exercise, including the converse of
  Tau Ceti's `Compatible.hermitianCore`, and the straight line between two
  forms that tame one complex structure, which *Symplectic vector bundles*
  uses too),
  `Analysis/InnerProductSpace/Symplectic/PolarComplexStructure/` (`Basic.lean`:
  $J_{g,\omega}$ for an arbitrary inner product $g$ given as a bilinear form,
  its equivariance under $\mathrm{GL}(V)$, and the lemma identifying it, for
  the ambient inner product, with Tau Ceti's `polarComplexStructure`; Tau
  Ceti's `TauCeti.SymplecticForm.polarComplexStructure_transport` gives the
  equivariance in that case; `Smooth.lean`: its explicit formula and
  smoothness),
  `Analysis/InnerProductSpace/LinearMap.lean` (`simp` for `innerSL ℝ` at
  the real bilinear type),
  `Topology/Algebra/Module/InnerProducts.lean` (the space $\mathrm{Met}(V)$
  of all inner products on $V$, a convex open subset of the symmetric bilinear forms,
  from Tau Ceti's `TauCeti.convex_setOfPred_symm_pos`),
  `Topology/Algebra/Module/SymplecticForms.lean` (the topology on
  `SymplecticForm V`), with the general file
  `Topology/Algebra/Module/BilinearForm.lean` (a continuous bilinear form in
  finite dimensions is recovered from its bilinear form; the skew part of a
  continuous bilinear map; carrying a form along an equivalence; the adjoint
  `ContinuousLinearMap.bilinAdjoint` of a map for two forms) and
  `LinearAlgebra/SesquilinearForm.lean` (an alternating form minus its
  transpose is twice the form),
  `Geometry/Symplectic/Darboux/EuclideanBasis.lean` (the coordinates of a
  basis adapted to $J$ are complex linear),
  `Geometry/Symplectic/Cayley/Domain.lean` (the open set where Tau Ceti's
  Cayley path is smooth),
  `Topology/ComplexStructure/Compatible/` (`Matrix.lean`: the identification
  $J\mapsto-J_0J$ with the symmetric positive definite symplectic matrices,
  by linear formulas; `Metric.lean` and `SymplecticForms.lean`: the homotopy
  equivalences with $\mathrm{Met}(V)$ and between forms and complex
  structures for fixed $g$; `Tame.lean`: the inclusion of compatible into
  tame structures as a homotopy equivalence; the contractions are explicit
  maps, not only Tau Ceti's contractibility instances, see below),
  `Topology/Algebra/Matrix/SymplecticGroup/CompactSubgroup.lean`
  (a compact subgroup of the symplectic group lies in some conjugate of
  $\mathrm{U}(n)$, from Tau Ceti's
  `exists_compatible_forall_isComplexLinearMap` and the transport of a
  compatible pair to $(\omega_0,J_0)$), with the general file
  `Topology/Algebra/Matrix/GeneralLinearGroup.lean` (the standard
  representation of `GL ι 𝕜` on `EuclideanSpace 𝕜 ι` as a continuous
  representation, `Matrix.GeneralLinearGroup.contRep`; it imports only
  Mathlib and Tau Ceti, and belongs upstream beside Tau Ceti's
  `MaximalCompact.lean`, whose private version of it it makes public).
- **Builds on:** *Standard model*; *Symplectic vector spaces* for the
  Lagrangian extension lemma, used in one characterization. Besides, it uses
  four merged files of *Linear complex structures*:
  `LinearAlgebra/Symplectic/Compatible.lean` imports
  `LinearAlgebra/ComplexStructure/Action.lean`, for
  `AlmostComplexStructure.transport_eq_iff_isComplexLinearMap` in the
  standard-model characterization;
  `Topology/ComplexStructure/Compatible/Matrix.lean` imports
  `Topology/ComplexStructure/Basic.lean`, for
  `AlmostComplexStructure.homeomorphMatrix`;
  `Topology/Algebra/Matrix/SymplecticGroup/CompactSubgroup.lean` imports
  `LinearAlgebra/ComplexStructure/Standard.lean`, for
  `stabilizer_stdComplexStructure`; and
  `Topology/ComplexStructure/Compatible/SymplecticForms.lean` imports
  `Topology/ComplexStructure/Orthogonal.lean`, for
  `metricComplexStructures_innerSL`. `Action.lean` imports only Mathlib and
  Tau Ceti, `Topology/ComplexStructure/Basic.lean` only `Action.lean`, Tau
  Ceti and the merged `LinearAlgebra/Matrix/NonsingularInverse.lean` and
  `Analysis/CStarAlgebra/Matrix.lean`, which import only Mathlib and merged
  files that do, `Standard.lean` and `Orthogonal.lean` only merged files, as the
  build-order table lists, so the part waits for nothing of *Linear complex structures*. `Compatible/Matrix.lean` also
  imports the merged `LinearAlgebra/Matrix/SymplecticGroup/Basic.lean` of
  *Symplectic group*, for `Matrix.IsSymm.mem_symplecticGroup_iff`.
- **Milestones:** *Characterizations of compatible complex structures*,
  *Contractibility of the space of compatible complex structures*, *Complex
  structures versus symplectic forms*, *Compact subgroups of the symplectic
  group*, *Contractibility of the space of tame complex structures*.
- **The design file decides:** the topology on spaces of forms and complex
  structures (the finite-dimensional topology of `V →ₗ[ℝ] V` and of bilinear
  forms, as Tau Ceti's contractibility instances use the operator norm; it
  checks they agree with Tau Ceti's topology on `AlmostComplexStructure`);
  how the milestones' smoothness and diffeomorphism conjuncts are stated (as
  manifold structures, or as `ContDiff` of the maps in coordinates; the
  nondegenerate forms and the inner products are open in their
  finite-dimensional spaces, but the complex structures lie in the closed set
  $\{J^2=-1\}$ of $\mathrm{End}(V)$, of positive codimension, so for them the
  file chooses between a submanifold structure and maps defined on an open
  neighbourhood in $\mathrm{End}(V)$). The design file chooses explicit
  formulas that are smooth on open sets: the Cayley path, Tau Ceti's
  `cayleyPathFormula`, on `SymplecticGeometry.cayleyDomain`
  (`Geometry/Symplectic/Cayley/Domain.lean`), and $(g,\omega)\mapsto
  J_{g,\omega}$ as `SymplecticGeometry.metricPolarFormula` on `SymplecticGeometry.polarDomain`
  (`PolarComplexStructure/Smooth.lean`), an open set that contains every
  pair of an inner product and a symplectic form. These three and the
  openness lemma below are the library's own declarations, not Tau Ceti API,
  so they are in `SymplecticGeometry`;
  `TauCeti.SymplecticForm.Compatible.mem_cayleyDomain` below is in the
  namespace of Tau Ceti's `SymplecticForm.Compatible`.
  The two Cayley-transform contractions, taken relative to a reference
  structure $J_0$, are given on the set $U_{J_0}$ of $A\in\mathrm{End}(V)$ such that $1-J_0A$ is invertible
  and $1-b\cdot$`cayleyFormula J₀ A` is invertible for every $b\in[0,1]$: the
  two units that `contDiffAt_cayleyPathFormula`
  (`Geometry/Symplectic/Cayley/Smooth.lean`) asks for. This set is open,
  since $[0,1]$ is compact (`SymplecticGeometry.isOpen_setOf_forall_Icc_mem_cayleyDomain`
  in `Cayley/Domain.lean`, stated for the pairs $(J_0,A)$). It
  does not contain every complex structure ($A=-J_0$ gives $1-J_0A=0$), but
  for an $\omega$-compatible $J_0$ it contains the $\omega$-tame structures,
  hence the compatible ones. The first unit is
  `Tames.isUnit_one_sub_mul_of_toLinearMap`, which needs $J_0$ only tame; the
  second is `Compatible.isUnit_one_sub_smul_cayleyFormula`, which needs $J_0$
  compatible (both in `Geometry/Symplectic/Cayley/Smooth.lean`). The
  contractions also take a compatible $J_0$, as Tau Ceti's do. The formulas
  are $C^\infty$ on their domains in the structure (and $J_{g,\omega}$ also
  in $g$). *Symplectic vector bundles* applies Tau Ceti's linear
  `cayleyPathFormula` and `SymplecticForm.polarComplexStructure` fibrewise
  (see that part), and reads `metricPolarFormula` on `polarDomain` in
  trivializations of its bundle of bilinear forms, where the form varies in
  the fibre; the smoothness of its $J_{g,\omega}$ and of $J_{g,\omega_{g,B}}$
  on its endomorphism bundle both come from that one reading. So its
  existence issue waits for the two issues of this part that write
  `PolarComplexStructure/`. It uses the same set $U_{J_0}$ at each point, and
  takes its openness from `SymplecticGeometry.isOpen_setOf_forall_Icc_mem_cayleyDomain`
  and the membership of the tame structures from
  `TauCeti.SymplecticForm.Compatible.mem_cayleyDomain`, so its
  contractibility issue waits for the issue of this part that writes
  `Cayley/Domain.lean`. Its homotopy-equivalence issue uses both, so it
  waits for the issues that write `Cayley/Domain.lean` and
  `PolarComplexStructure/`.

### 10. Linear Moser

- **Files:** `Geometry/Symplectic/LinearMoser.lean`, and
  two general facts it uses: the derivative of a path of skew forms is skew
  (`Analysis/Calculus/Deriv/ContinuousLinearMap.lean`), and the derivative of
  a path with locally constant square anticommutes with it
  (Tau Ceti's `TauCeti.mul_fderiv_add_fderiv_mul_eq_zero`). Given nondegenerate
  forms $\omega_t$ on $V$ that depend smoothly on $t\in\mathbb{R}$, the first file builds
  invertible $\Psi_t$, smooth in $t$, starting at the identity and pulling
  each $\omega_t$ back to $\omega_0$: $\Psi_t$ solves $\dot\Psi_t=A_t\Psi_t$,
  with $A_t=-\tfrac12\,\omega_t^{-1}\circ\dot\omega_t$, the inverse being that
  of the contraction $V\to V^*$, so that no inner product is needed. The
  same file treats a smooth path of complex structures in the same way. If
  the bundle case needs smoothness in a parameter as well, the parametric
  version goes in `Analysis/ODE/DysonSeries.lean`, in the namespace
  `SymplecticGeometry` (the lemma is about the function `dysonSeriesLeft`,
  which dot notation does not reach, and a name in `TauCeti` could clash with
  a later Tau Ceti lemma), extending `TauCeti.continuous_parametric_dysonSeriesLeft`
  from continuity to smoothness. Before a series proof, that issue checks
  whether Tau Ceti's `ODE.exists_contDiffOn_picard_solution`
  (`Analysis/ODE/SmoothParameter.lean`) or `TauCeti.contDiff_timeDependentFlow`
  (`Dynamics/Flow/Variational.lean`) already gives it.
- **Builds on:** Tau Ceti's linear equations (`Analysis/ODE/DysonSeries.lean`):
  `TauCeti.dysonSeriesLeft` solves $\dot\Gamma=p\,\Gamma$,
  `TauCeti.contDiff_dysonSeriesLeft` gives a $C^{n+1}$ solution for a $C^n$
  coefficient, and `TauCeti.eq_dysonSeriesLeft_apply` gives uniqueness. So
  this part needs no general ODE theory of its own beyond the parametric
  lemma, which is general material and sits in its own file. It uses no other
  part, except `Topology/Algebra/Module/BilinearForm.lean` of *Compatible
  complex structures* (`ContinuousLinearEquiv.bilinearCongr`), which imports
  only Mathlib and Tau Ceti and is merged.
- **Milestones:** *Linear Moser lemma*.
- The construction is canonical, a formula in the family and its derivative,
  so that *Symplectic vector bundles* can apply it at each point of the base.

### 11. Siegel upper half space

- **Files:** `Analysis/Complex/SiegelUpperHalfSpace/Basic.lean` (the space
  $\mathcal{S}_n$ of complex symmetric matrices with positive definite
  imaginary part), `.../Action.lean` (the action of $\mathrm{Sp}(2n)$ by
  $(AZ+B)(CZ+D)^{-1}$, its holomorphy and transitivity, the stabilizer of
  $i\mathbb{1}$), `.../ComplexStructure.lean` (the equivariant bijection with
  the compatible complex structures on `StdSpace ι` and its explicit formula).
  For $n=1$ it is compared with Mathlib's `UpperHalfPlane` action and with Tau
  Ceti's `stdComplexSymplecticForm_tames_iff_im_pos`.
  Six general files about matrices, outside the part's folder, serve it:
  `LinearAlgebra/Matrix/PosDef/Basic.lean` (`Matrix.posDef_iff_of_unique`:
  over an index type with one element, a matrix is positive definite exactly
  when its entry is positive), `LinearAlgebra/Matrix/PosDef/Block.lean`
  (`Matrix.posDef_fromBlocks_zero_zero_iff` and its semidefinite analogue:
  `fromBlocks A 0 0 D` is positive (semi)definite exactly when $A$ and $D$
  are; `Matrix.PosDef.toBlocks₁₁` and `Matrix.PosDef.toBlocks₂₂`: the
  diagonal blocks of a positive definite matrix are positive definite), `LinearAlgebra/Matrix/PosDef/OfReal.lean`
  (`Matrix.posDef_map_algebraMap_iff` and `Matrix.posDef_map_ofReal_iff`: a
  real matrix is positive definite exactly when its image over an `RCLike`
  field is, through Tau Ceti's realification),
  `LinearAlgebra/Matrix/Symmetric.lean` (`Matrix.IsSymm.sub_conjTranspose`:
  $Z-Z^{*}=2i\,\mathrm{Im}\,Z$ for a symmetric complex $Z$, and
  `Matrix.isSymm_mul_nonsing_inv_of_transpose_mul_eq`: $AB^{-1}$ is symmetric
  when $A^{T}B=B^{T}A$),
  `LinearAlgebra/Matrix/Block.lean` (the two identities between the blocks
  of $M$ that the first block column of $M^2=-1$ gives), and
  `Topology/Instances/Matrix.lean` (`Continuous.isOpen_setOf_isUnit_det`:
  for a continuous family $f$ of square matrices over a topological field
  with closed points, the parameters $x$ where $f(x)$ is invertible form an
  open set; and its two consequences `Matrix.isOpen_setOf_isUnit_det_map_im`
  and `Matrix.isOpen_setOf_isUnit_det_toBlocks₂₁`: the complex matrices
  with invertible imaginary part, and the block matrices over such a field
  whose square lower left block is invertible, are open). They import only Mathlib, Tau Ceti and each other.
- **Builds on:** *Standard model*; compatibility is Tau Ceti's `Compatible`.
  It also depends on five files of three other parts. `Basic.lean` (for
  `Matrix.map_re_add_I_smul_map_im`, $Z = X + iY$) and `Action.lean` import
  `LinearAlgebra/Matrix/OfReal.lean`, the general matrix file of
  *Lagrangian Grassmannian* on reading real matrices as complex ones.
  `ComplexStructure.lean` imports
  `LinearAlgebra/Matrix/SymplecticGroup/Basic.lean` from *Symplectic group*
  and two files of *Linear complex structures*:
  `LinearAlgebra/ComplexStructure/Action.lean` and
  `LinearAlgebra/ComplexStructure/Standard.lean` (from which it uses that an
  invertible symplectic matrix preserves and reflects compatibility with
  $\omega_0$, `compatible_generalLinearGroup_smul_iff`). The first three
  import only Mathlib and Tau Ceti. `Standard.lean` imports
  `ComplexStructure/Action.lean`, the *Standard model* file
  `LinearAlgebra/Symplectic/Standard/Matrix.lean`
  and a third file of *Linear complex structures*, the library's
  `Geometry/Symplectic/Orientation.lean` (not Tau Ceti's file of the same
  path), which imports only Tau Ceti; it also imports
  `LinearAlgebra/Symplectic/Compatible.lean` of *Compatible complex
  structures*, which besides Mathlib and Tau Ceti imports only
  `ComplexStructure/Action.lean`, the Tau-Ceti-only
  `Geometry/Symplectic/Darboux/EuclideanBasis.lean` of *Compatible complex
  structures* (not Tau Ceti's file of the same path),
  `Symplectic/Standard/Basic.lean` of *Standard model* and
  `Symplectic/Subspace.lean` of *Symplectic vector spaces*. All these files
  are merged. So the part needs only level-0 parts
  and merged files of other parts, and still sits at level 1.
- **Milestones:** *Siegel upper half space*. The proof of transitivity checks
  the formula for $J(Z)$ directly, which breaks the circularity between the
  book's exercise and lemma that the plan points out. The milestone's
  smoothness conjuncts are stated as `ContDiff` of the bijection and its
  inverse in coordinates (symmetric matrices on one side, matrices on the
  other), a decision that the issue for `ComplexStructure.lean` makes
  precise.

### 12. Symplectic vector bundles (needs `design/symplectic-vector-bundles.md`)

- **Files:** `Geometry/Manifold/VectorBundle/Symplectic/Basic.lean`
  (symplectic forms on a smooth real vector bundle, as smooth sections of the
  bundle of alternating maps, Mathlib's
  `ContMDiffVectorBundle.continuousAlternatingMap`, that are fibrewise
  nondegenerate; transport along isomorphisms; for $E=TM$, the
  identification of these forms with Tau Ceti's `TauCeti.SmoothTwoForm I M`
  and of nondegeneracy with `TauCeti.SmoothTwoForm.IsNondegenerate`; the
  nondegeneracy criterion for forms on bundles of rank two, and
  with it the tangent bundle of a surface with an area form; see
  *Constructions* below),
  `.../Symplectic/Pullback.lean` and `.../Symplectic/Prod.lean` (pull-backs
  and direct sums of forms, with their tame and compatible pairs,
  isomorphisms and frames; see *Constructions*),
  `Geometry/Manifold/VectorBundle/Pullback.lean` (the smoothness criterion
  for sections of the bundle of alternating maps of a pull-back, in the root
  namespace `Bundle.Pullback`; the file has the name of the Tau Ceti file
  with the criterion for Hom sections, so that the two merge upstream),
  `Geometry/Manifold/VectorBundle/Prod.lean` (smoothness on total spaces of the
  fibrewise product of two maps and of the swap of a direct-sum bundle, for
  fibres with only a zero, and for bundle isomorphisms as
  corollaries, in the root namespace `Bundle.Prod`; the file has the path of the
  Tau Ceti file with the product criterion, so that the two merge upstream),
  `Topology/VectorBundle/Pullback.lean` (the coordinates of alternating maps
  on a pull-back bundle, a step that uses no charts, and
  `Bundle.Pullback.neg_fiber` and its companions for sums, differences,
  multiples and zeros, which take each operation in a fibre of a pull-back
  bundle at the type of its arguments; it imports `Data/Bundle.lean`; the
  file has the path of the Tau Ceti file with
  `ContinuousLinearMap.inCoordinates_pullback_of_mem`,
  so that the two merge upstream),
  `Topology/VectorBundle/Coordinates.lean` (the coordinates of continuous
  bilinear forms on a vector bundle; the file has the path of the Tau Ceti
  file with `ContinuousLinearMap.inCoordinates_eq_conjContinuousAlgEquiv`,
  so that the two merge upstream),
  `Data/Bundle.lean` (`Bundle.Pullback.eq_iff`, an equation in a fibre of a
  pull-back bundle as one in the fibre it is defined as, and
  `Bundle.Pullback.eq_fiber_iff`, which states an equation between vectors
  of a fibre of a pull-back bundle in that fibre, and
  `Bundle.Pullback.neg_apply_fiber` and `neg_apply_pullback`, which evaluate
  a negated function on a vector of the other fibre type, in the root
  namespace and at the path of the Mathlib file that defines
  `Bundle.Pullback`),
  `Geometry/Manifold/VectorBundle/Hom.lean` (for fibrewise equivalences
  whose map of total spaces is $C^n$, the $C^n$ section of the hom bundle
  formed by their inverses, `contMDiff_hom_bundle_symm`, in the
  namespace `SymplecticGeometry`; the file has the name of the Tau Ceti file with
  `TauCeti.contMDiff_hom_bundle_iff`, so that the two merge upstream),
  `Geometry/Manifold/VectorBundle/ContinuousAlternatingMap.lean`
  (precomposition with a $C^n$ section of a hom bundle as a $C^n$ map of the
  total spaces of bundles of alternating maps,
  `contMDiff_compContinuousLinearMap_totalSpace`, in `SymplecticGeometry`, and
  `Bundle.flatAt` and `Bundle.alternatingMapOfBilin` between alternating and
  bilinear maps of two vectors, $C^n$ along a map; the
  file has the name of the Mathlib file that defines
  `ContMDiffVectorBundle.continuousAlternatingMap`, so that the two merge
  upstream),
  `Topology/FiberBundle/Basic.lean` (a fibrewise open condition on a fibre
  bundle gives an open set of the total space, in Mathlib's namespace),
  `Topology/FiberBundle/ChangeModelFiber.lean` (a fibre bundle read with
  another model fibre along a homeomorphism, in Mathlib's namespaces and at
  Mathlib's fibre-bundle level, since it involves no group),
  `Topology/FiberBundle/Principal/ChangeGroup.lean` (the change of structure group
  of a Tau Ceti principal bundle along an isomorphism of topological groups,
  in the namespaces of the Tau Ceti and Mathlib types it is about; it sits
  in the Tau Ceti folder of principal bundles, so that it can merge there),
  `Geometry/Symplectic/Manifold/Volume.lean` (the symplectic orientation of
  a negated two-form, in Tau Ceti's namespace; the file has the name of the
  Tau Ceti file that defines `volumeOrientation`),
  `Analysis/CStarAlgebra/Unitary/ContinuousLinearMap.lean` (for `RCLike 𝕜`,
  `Unitary.continuousLinearMapSelfEquiv`, the isomorphism of topological
  groups from the unitaries of `𝕜 →L[𝕜] 𝕜` to those of `𝕜`, and its case
  `Unitary.continuousLinearMapCircleEquiv` onto `Circle`, in Mathlib's
  namespace `Unitary`; see *Constructions*),
  `Analysis/InnerProductSpace/GramSchmidtOrtho.lean` (for a skew-adjoint
  orthogonal `J`, Mathlib's Gram–Schmidt turns `u₀, J u₀, u₁, J u₁, …` into
  `e₀, J e₀, e₁, J e₁, …`,
  in Mathlib's namespace `InnerProductSpace`; the file has the name of the
  Mathlib file that defines `gramSchmidt`),
  `Topology/VectorBundle/LinearIndependent.lean` (sections continuous and
  linearly independent at a point stay independent near it, in Mathlib's
  namespace `Bundle.Trivialization`),
  `Analysis/Normed/Operator/SpanSingleton.lean`
  (`LinearIsometryEquiv.toSpanSingleton`, a unit vector of a line as a
  linear isometry from the scalars),
  `Geometry/Manifold/VectorBundle/ComplexStructure.lean` (the one model of
  $C^n$ complex structures on a bundle, `SymplecticGeometry.Bundle.ContMDiffComplexStructure`,
  generalizing from $TM$ to any bundle Tau Ceti's
  `TauCeti.ContMDiffAlmostComplexStructure I n M`
  (`Geometry/Symplectic/Manifold/AlmostComplex/ContMDiff.lean`) with the same
  field names, `toEndomorphism` and `square_neg`, and the same `n : ℕ∞`, and
  following `TauCeti.SmoothAlmostComplexStructure`
  (`Geometry/Symplectic/Manifold/AlmostComplex/Basic.lean` and `Topology.lean`)
  for the topology: a $C^n$ section `toEndomorphism` of the endomorphism
  bundle with square $-1$, `@[ext]` through it, the topology `frameTopology`
  induced from `ContMDiffSection.frameTopology`, and
  `isClosedEmbedding_toEndomorphism_frameTopology`; the map to Tau Ceti's
  `TauCeti.Bundle.ContinuousComplexStructure`, so that its complex bundle is
  available; its pull-back, direct sum, and the structure of multiplication
  by `Complex.I` on a complex bundle (see *Constructions*); and for $E=TM$,
  for every $n$, the identification with
  `ContMDiffAlmostComplexStructure I n M`, under which the map to
  `ContinuousComplexStructure` is Tau Ceti's
  `ContMDiffAlmostComplexStructure.toContinuousComplexStructure`
  (`AlmostComplex/ComplexTangentBundle.lean`), and for $n=\infty$, composed
  with `ContMDiffAlmostComplexStructure.smoothEquiv`, the homeomorphism with
  `SmoothAlmostComplexStructure` for the two `frameTopology`s, so that
  manifolds keep Tau Ceti's models),
  `.../Symplectic/ComplexStructure/` (`Basic.lean`: tame and compatible
  pairs, as predicates like Tau Ceti's for $TM$, the form $\omega_{g,J}$ of a
  metric and a structure, the polar structure $J_{g,\omega}$, built fibrewise
  from Tau Ceti's linear `SymplecticForm.polarComplexStructure`, and the
  existence of compatible structures and forms; `Contractible.lean`:
  contractibility of the tame and compatible structures for a fixed form and
  of the taming and compatible forms for a fixed structure, the homotopy
  equivalence $\omega\mapsto J_{g,\omega}$ on sections, and the second
  milestone),
  `Geometry/Manifold/VectorBundle/Riemannian/SectionTopology.lean`
  (contractibility of $\mathrm{Met}(E)$, Mathlib's
  `Bundle.ContMDiffRiemannianMetric` with Tau Ceti's
  `Bundle.ContMDiffRiemannianMetric.frameTopology`, from
  `continuous_convexCombination_frameTopology`; the file has the name of the
  Tau Ceti file with that lemma, since it mentions only Mathlib and Tau Ceti
  types),
  `Geometry/Manifold/VectorBundle/Riemannian/PolarEnd.lean` (for a bundle
  metric $g$, the polar formula $J_{g,\sigma}$ on the bundle of bilinear
  forms, `polarFormulaAt` on the open set `Bundle.polarFormulaDomain`, smooth
  there by `contMDiffOn_polarFormulaAt`, which reads part 9's
  `metricPolarFormula` in trivializations; from it come both the smoothness
  of `polarComplexStructure` and the structure $J_{g,\omega_{g,B}}$ on the
  endomorphism bundle, `polarEndAt` on the open set `polarEndDomain`; it
  mentions no symplectic form on the bundle, so it sits apart from the
  symplectic files),
  `.../Symplectic/Trivialization.lean` (local Darboux frames, by a
  symplectic Gram–Schmidt on sections, local symplectic trivializations and
  the reduction of the structure group to $\mathrm{Sp}(F,\sigma)$),
  `.../Symplectic/Classification.lean` (two symplectic bundles
  with tame complex structures are isomorphic as symplectic bundles if and
  only if they are as complex bundles),
  `Geometry/Manifold/VectorBundle/Section/Topology.lean` (the general lemma,
  in the namespace `ContMDiffSection`: for fibre maps
  $\Phi_{p,x}:V_x\to W_x$ depending on a parameter $p$ in a manifold $P$,
  defined on an open subset $O$ of the total space of $V$ and jointly $C^n$
  there in the parameter, the point and the fibre value, the map
  $(p,s)\mapsto\Phi_p\circ s$ from $P$ times the sections with values in $O$
  to `Cₛ^n⟮I; F', W⟯` is jointly continuous for `frameTopology`, for every
  $n$ including $\infty$. Joint regularity implies that the derivatives in
  the fibre directions are continuous in $p$, and it is what the uses give,
  since their fibre maps are explicit formulas. Openness in each fibre would
  not do, since derivatives in trivializations need an open set of the total
  space. Examples are the union over $x\in M$ of the sets $U_{J_0(x)}$ of
  the two Cayley units, for a continuous reference structure $J_0$
  compatible with the form, which contains the tame structures, and the
  fibrewise nondegenerate forms. Continuity in the point alone is not
  enough for $n\ge1$: on the
  trivial line bundle over $\mathbb{R}$, $\Phi_t(x,v)=v+t\sin(x/t)$ is
  continuous in $(t,x,v)$ with $\Phi_0=\mathrm{id}$, but
  $\partial_x(\Phi_t\circ s-s)=\cos(x/t)$ does not tend to $0$. The proof
  goes through `ContMDiffSection.continuous_frameTopology_iff_frameCoordinates`;
  the file has the name of the Tau Ceti file that defines that topology, so
  that the two merge upstream),
  `Geometry/Manifold/ContMDiffMap/Chart/CodRestrict.lean` (corestriction of
  a $C^n$ map to an open subset of its target, continuous for Tau Ceti's
  weak Whitney topology; a step of the proof of the previous lemma, placed
  beside Tau Ceti's weak Whitney files so that it can merge there),
  `Geometry/Manifold/ContMDiffMap/Chart/Restriction.lean` (ambient chart
  derivatives of a function that agrees on an open set with a $C^n$ map on
  it, and their convergence in the weak Whitney topology; another step of
  the proof of that lemma, generalizing the lemmas of Tau Ceti's file of the
  same name and sitting beside it so that the two can merge),
  `Geometry/Manifold/VectorBundle/Cayley.lean` (smoothness of Tau Ceti's
  `cayleyPathFormula` as a map into the endomorphism bundle of any vector
  bundle, along a base map, at every order, generalizing by the same proof
  Tau Ceti's `ContMDiffAt.cayleyPathFormula_hom_bundle`, which is the case
  of $TM$ at order $\infty$; it supplies the joint regularity that the lemma of
  `Section/Topology.lean` asks for in the contractibility proofs; and
  `Bundle.cayleyPathDomain`, the set of points $q$ of the total space at
  which, read in a trivialization, the triple of a coefficient $b$, the
  reference endomorphism at $q$ and the fibre value of $q$ lies in part 9's
  `SymplecticGeometry.cayleyDomain` for every $b\in[0,1]$. Its intersection with an
  open set on which the reference is continuous is open
  (`Bundle.isOpen_cayleyPathDomain`, from part 9's
  `SymplecticGeometry.isOpen_setOf_forall_Icc_mem_cayleyDomain`), and it contains
  every structure on a fibre that is tame for a form there when the
  reference is compatible with that form
  (`TauCeti.SymplecticForm.Compatible.mem_cayleyPathDomain`, from
  `TauCeti.SymplecticForm.Compatible.mem_cayleyDomain`); the
  contractibility proofs take their open set from it. The file mentions no
  symplectic form on the bundle, so it sits apart from the symplectic
  files),
  `Geometry/Manifold/VectorBundle/Hermitian/Basic.lean` (the symplectic form
  of a Hermitian bundle; see *Constructions* below),
  `Geometry/Manifold/VectorBundle/Riemannian/Trivial.lean` (the constant
  metrics `Bundle.ContMDiffRiemannianMetric.const` on a trivial bundle and
  `constComplexEuclidean` on `Bundle.Trivial M (ι → ℂ)`, in
  the root namespace since it involves only Mathlib's types; neither Mathlib
  nor Tau Ceti has one, and the standard case of the form of a Hermitian
  bundle needs it),
  `.../Hermitian/CircleBundle.lean` (the unit circle bundle of a Hermitian
  line bundle as a principal `Circle`-bundle; see *Constructions*),
  and, for the last milestone, `Geometry/Manifold/IsManifold/InteriorBoundary.lean`
  (the interior of a manifold with boundary as a boundaryless manifold,
  connected when the manifold is connected; its topological step goes in
  `Topology/Connected/Clopen.lean`),
  `Geometry/Manifold/Boundary/Collar/Push.lean`
  (a homotopy pushing a compact manifold with boundary into a compact subset
  of its interior along a collar),
  `Geometry/Diffeomorphism/Diffeotopy/Discrete.lean` (a diffeotopy of a
  connected boundaryless manifold whose final map sends a compact set off a
  closed discrete set), `.../VectorBundle/Section/Generic.lean`
  (over a boundaryless manifold, a smooth section of a bundle of rank equal
  to the dimension whose zero set is closed and discrete),
  `.../VectorBundle/Section/Nonvanishing.lean` (a smooth nowhere-zero section of
  every real bundle of rank at least $2$ over a compact, connected surface
  whose boundary is not empty) and
  `Geometry/Manifold/VectorBundle/Hermitian/Surface.lean` (unitary frames
  and trivializations over compact connected surfaces with nonempty
  boundary, not assumed oriented, by induction on the rank through Hermitian
  orthogonal complements). The book's route cuts the surface into pieces,
  which would need the classification of compact surfaces with boundary;
  this route needs only the nowhere-zero sections. Lemma 2.6.6 of
  [McDuffSalamon2017], unitary frames along curves, is not used and not
  planned; *First Chern number* does not use it either. The parametric
  smoothness of the linear Moser flow, which the classification uses, goes
  in the files of *Linear Moser*.
- **Builds on:** *Linear Moser*, *Standard model* (`stdForm`,
  `StdSpace.sumEquiv` and the matrix dictionary, for frames and
  transition maps), Mathlib's
  smooth vector bundles and bundle metrics, Tau Ceti's bundle constructions
  (`Topology/VectorBundle/`, `Geometry/Manifold/VectorBundle/`), its section
  spaces with their topology (`Geometry/Manifold/VectorBundle/Section/`), the
  topology on bundle metrics
  (`Geometry/Manifold/VectorBundle/Riemannian/SectionTopology.lean`), its
  almost complex structures on $TM$ with their topology and their tame and
  compatible subtypes
  (`Geometry/Symplectic/Manifold/AlmostComplex/Topology.lean`), its $C^n$
  almost complex structures on $TM$ and their map to continuous complex
  structures (`Geometry/Symplectic/Manifold/AlmostComplex/ContMDiff.lean`,
  `.../AlmostComplex/ComplexTangentBundle.lean`), and its other
  results for $E=TM$ (`Geometry/Symplectic/Manifold/`), which it generalizes
  rather than duplicates; its linear Cayley path (`cayleyPathFormula` with
  its unit lemmas, `Geometry/Symplectic/Cayley/`) and polar complex
  structure (`SymplecticForm.polarComplexStructure`), applied fibrewise;
  its generic sections, diffeotopies of configurations and collars, for the
  last milestone; for the constructions, the pieces listed under
  *Constructions*. From *Compatible complex structures* it uses the file
  `Geometry/Symplectic/Cayley/Domain.lean` (`SymplecticGeometry.cayleyDomain`, its
  openness lemma `SymplecticGeometry.isOpen_setOf_forall_Icc_mem_cayleyDomain` and
  `TauCeti.SymplecticForm.Compatible.mem_cayleyDomain`), and the two files of
  `Analysis/InnerProductSpace/Symplectic/PolarComplexStructure/`
  (`SymplecticGeometry.metricPolarFormula` on `SymplecticGeometry.polarDomain`, with its smoothness
  and naturality) for `polarFormulaAt`, and so for the smoothness of
  `polarComplexStructure` and for `polarEndAt`.
  Its existence issue waits for the two issues of that part that write
  `PolarComplexStructure/`; its contractibility issue waits for the issue of
  that part that writes `Cayley/Domain.lean`, which has no blockers; its
  homotopy-equivalence issue waits for that one and for the two that write
  `PolarComplexStructure/`.
- **Milestones:** *Symplectic vector bundles are complex vector bundles*,
  *Compatible and tame complex structures on symplectic vector bundles*,
  *Unitary trivializations over surfaces with boundary*.
- **Topology on sections.** The milestones' spaces of sections are subspaces
  of Tau Ceti's section spaces `Cₛ^n⟮I; F, V⟯` (of the bundle of
  endomorphisms, or of alternating maps) with
  `ContMDiffSection.frameTopology` (`Section/Topology.lean`): uniform
  convergence on compact sets of the frame coefficients and of all their
  derivatives up to order $n$. For $n=0$ this is the compact-open $C^0$
  topology, and for $n=\infty$ the compact-open $C^\infty$ topology; the
  milestones are stated for both. The topology is defined from a choice of
  frame domains covering $M$, and
  `ContMDiffSection.frameTopology_eq_of_covers` (`Section/FrameCover.lean`)
  shows it does not depend on the choice, so the statements fix any such
  cover. They are `ContractibleSpace` and `ContinuousMap.HomotopyEquiv` for
  these subspaces. The proofs apply explicit linear formulas at each point:
  Tau Ceti's `cayleyPathFormula` and `SymplecticForm.polarComplexStructure`,
  convex combinations, and the linear Moser construction of *Linear Moser*.
  For complex structures, the Cayley path relative to a reference structure
  $J_0$ compatible with the form is jointly smooth in its coefficient and the
  structure on the sets $U_{J_0(x)}$ of the two Cayley units, which form an
  open subset of the total space of the endomorphism bundle (the two units
  are open conditions and $[0,1]$ is compact) containing the values of
  every tame structure. Tau Ceti's second unit holds only for coefficients
  in $[-1,1]$, so the time enters through `smoothTransition`, which keeps
  the coefficient in $[0,1]$ for every real time, and the homotopies are the
  restrictions to $[0,1]$. Read in trivializations these maps are then
  jointly $C^n$ in the time, the point and the fibre value, which is the
  hypothesis of the lemma of `Section/Topology.lean`. That lemma makes the
  induced maps on sections, and the contractions $[0,1]\times S\to S$ as a
  whole, continuous for `frameTopology`;
  `ContMDiffSection.continuous_totalSpace_eval` and
  `locallyConvexSpace_frameTopology` give the evaluation and the convex
  combinations.
- **Constructions.** *First Chern number* needs four ways to make symplectic
  bundles, which this part provides, in the namespace
  `SymplecticGeometry.Bundle` unless a name says otherwise. None of them is
  a new type of bundle: each is a form, a complex structure or a lemma on
  bundles that Mathlib or Tau Ceti already builds. Forms are elements of
  the type of two-forms on a bundle that `Symplectic/Basic.lean` defines
  (`ContMDiffTwoForm I n F E`, a $C^n$ section of the bundle of alternating
  maps, with the predicate `ContMDiffTwoForm.IsNondegenerate`), and the
  constructions on forms sit in its namespace, so that dot notation finds
  them; those on complex structures sit in `ContMDiffComplexStructure`, in
  `ComplexStructure.lean`, since they use no form.
  - *Pull-back* (`Symplectic/Pullback.lean`). For a `ContinuousMapClass` map
    `f` with `hf : ContMDiff I' I n f`, the
    pull-back of a form `ω` on `E` to `f *ᵖ E` (`Bundle.Pullback`) is
    `ContMDiffTwoForm.pullback ω f hf`, written `ω.pullback f hf`, with the
    section first as in Tau Ceti's `ContMDiffSection.pullback ω f`, of
    which it is that section read as a section of the bundle of
    alternating maps of `f *ᵖ E`: the fibres of the two bundles at `y` are
    both the alternating maps on `E (f y)`, and the new lemma
    `Bundle.Pullback.contMDiff_continuousAlternatingMap_section_iff`
    (`Geometry/Manifold/VectorBundle/Pullback.lean`, in the root namespace
    `Bundle.Pullback` and not under `SymplecticGeometry`, so that it sits
    beside Tau Ceti's lemma and moves upstream unrenamed), the analogue for
    alternating maps of Tau Ceti's
    `Bundle.Pullback.contMDiff_hom_section_iff`, says that the two
    smoothness conditions agree. API: `@[simp] pullback_apply` (the value at
    `y` is `ω (f y)`, from Tau Ceti's `ContMDiffSection.pullback_apply`),
    `IsNondegenerate.pullback`, and `symplecticFormAt` of the pull-back at
    `y` is that of `ω` at `f y`. For complex structures,
    `ContMDiffComplexStructure.pullback J f hf` (`ComplexStructure.lean`,
    `J.pullback f hf`, in the same order, for any `ContinuousMapClass` map
    `f` with `hf : ContMDiff I' I n f`) is
    `ContMDiffSection.pullback` of the endomorphism section, smooth by
    `Bundle.Pullback.contMDiff_hom_section_iff` itself, which `simp`
    evaluates through `@[simp] pullback_apply` and, given `hf`,
    `apply_eq_pullback_apply`; `Pullback.lean` adds that
    tame and compatible pairs pull back to tame and compatible pairs. Isomorphisms: a
    symplectic isomorphism of bundles pulls back to one (Tau Ceti's
    `Bundle.Pullback.contMDiff_fiberwise`), a symplectic frame over `U`
    pulls back to a frame over `f ⁻¹' U`, and the pull-backs along the
    identity and along `g ∘ f` are symplectically isomorphic to `ω` and to
    the iterated pull-back, through Tau Ceti's
    `Bundle.Pullback.idDiffeomorph` and `Bundle.Pullback.compDiffeomorph`.
  - *Direct sum* (`Symplectic/Prod.lean`). For forms `ω₁` on `E₁` and `ω₂`
    on `E₂`, the form `ContMDiffTwoForm.prod ω₁ ω₂` on Mathlib's
    `E₁ ×ᵇ E₂` (`Bundle.Prod`, with `Bundle.Prod.contMDiffVectorBundle`),
    which is Tau Ceti's linear `TauCeti.SymplecticForm.prod` in each fibre:
    `@[simp] prod_apply`, $(\omega_1\oplus\omega_2)((v_1,v_2),(w_1,w_2))=
    \omega_1(v_1,w_1)+\omega_2(v_2,w_2)$, `IsNondegenerate.prod`, and
    `symplecticFormAt` of the sum is `SymplecticForm.prod` of the two. For
    complex structures, `ContMDiffComplexStructure.prod J₁ J₂`
    (`ComplexStructure.lean`), fibrewise
    `TauCeti.AlmostComplexStructure.prod`; `Prod.lean` adds that tame and
    compatible pairs are preserved, by Tau Ceti's
    `SymplecticForm.prod_tames` and `SymplecticForm.prod_compatible`.
    Smoothness of maps into and out of the sum is Tau Ceti's criterion in
    `Geometry/Manifold/VectorBundle/Prod.lean`. Isomorphisms: the direct sum
    of two symplectic isomorphisms is one, and `E₁ ×ᵇ E₂` is symplectically
    isomorphic to `E₂ ×ᵇ E₁`. Block frames: symplectic frames `Φ₁` of `E₁`
    for `stdForm ι` and `Φ₂` of `E₂` for `stdForm κ` over a set `U` give the
    frame of the sum for `stdForm (ι ⊕ κ)` that is their product after
    `StdSpace.sumEquiv ι κ` (*Standard model*), and the transition map of
    two such block frames is, through `Matrix.toEuclideanLin`, the
    `Matrix.symplecticSum` of the two transition maps. So a transition loop
    of the sum is `TauCeti.GLSymplectic.sum` of the two loops, as
    `TauCeti.GLSymplectic.maslovIndex_sum` takes it. Tau Ceti's other
    Whitney sum, `TauCeti.FiniteRankBundleCore.whitneySum`, is a topological
    construction on bundle cores; this part does not use it, and its total
    space is identified with that of `×ᵇ` by Tau Ceti's
    `whitneySumTotalSpaceHomeomorph` where a comparison is needed.
  - *The tangent bundle of a surface with an area form*
    (`Symplectic/Basic.lean`, beside the identification with
    `TauCeti.SmoothTwoForm`). On a manifold `S` whose model space `E` has
    `finrank ℝ E = 2`, a smooth two-form `σ : TauCeti.SmoothTwoForm I S`
    that vanishes nowhere is, through that identification, a symplectic
    form on `TangentSpace I`. The criterion is stated for every bundle of
    rank two, since the proof is the same pointwise fact:
    `ContMDiffTwoForm.isNondegenerate_iff_forall_ne_zero_of_finrank_eq_two`,
    for `finrank ℝ F = 2`, says that `ω` is nondegenerate if and only if
    `ω x ≠ 0` for every `x`, by the pointwise step of Tau Ceti's
    `TauCeti.SmoothTwoForm.isNondegenerate_iff_forall_ne_zero_of_finrank_eq_two`.
    The tangent case is then `tangentEquiv.symm σ`, nondegenerate by
    `isNondegenerate_tangentEquiv_iff` and Tau Ceti's lemma.
    No definition is added. The orientation that `σ` induces is Tau Ceti's
    symplectic orientation `TauCeti.SmoothTwoForm.IsNondegenerate.volumeOrientation`
    with `n = 1`, and *First Chern number* states with it that an area form
    induces a given orientation; no second name for it is introduced. As it
    involves no bundle form, the lemma
    `TauCeti.SmoothTwoForm.IsNondegenerate.volumeOrientation_neg` goes in
    `Geometry/Symplectic/Manifold/Volume.lean`, in Tau Ceti's namespace so
    that it can move there: for odd
    `n`, the symplectic orientation of `-σ` (with Tau Ceti's
    `IsNondegenerate.neg`) is the negation of that of `σ`, since the volume
    form of `-σ` is $(-1)^n$ times that of `σ` and
    `Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff`
    reverses with the sign of the form.
  - *Hermitian bundles* (`Hermitian/Basic.lean`). A Hermitian bundle is
    represented as Tau Ceti does in
    `Geometry/Manifold/VectorBundle/Riemannian/LineSplitting.lean`: a complex
    vector bundle `[VectorBundle ℂ F V]`, smooth as a real bundle through
    `VectorBundle.restrictScalars`, with
    `g : Bundle.ContMDiffRiemannianMetric I n F V` and
    `hI : ∀ x v w, g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w`;
    a Hermitian line bundle is the case `finrank ℂ F = 1`. Multiplication by
    `Complex.I` is `ContMDiffComplexStructure.ofComplexModule`
    (`ComplexStructure.lean`, for any complex bundle, with no metric), whose
    section is smooth by Tau Ceti's `TauCeti.contMDiff_smulIEquiv_bundle`
    and whose map to `TauCeti.Bundle.ContinuousComplexStructure` gives back
    the complex structure of `V`. The form of the Hermitian bundle is no new
    definition: it is
    `(ContMDiffComplexStructure.ofComplexModule I n F V).compatibleForm g`,
    the form $\omega_{g,J}$ of tame and compatible pairs for $J$ the
    multiplication by `Complex.I`. Under `hI`, $g_x(v,iw)=-g_x(iv,w)$, so
    its value $\tfrac12(g_x(iv,w)-g_x(v,iw))$ is $g_x(iv,w)$
    (`compatibleForm_ofComplexModule_apply`). Its compatibility with
    `ofComplexModule`, nondegeneracy and smoothness are those of any
    `compatibleForm` (`compatible_compatibleForm`,
    `Compatible.isNondegenerate`). The lemmas stated for it, in
    `SymplecticGeometry.Bundle.ContMDiffComplexStructure` and all under
    `hI`: $\omega(v,iw)=g(v,w)$
    (`compatibleForm_ofComplexModule_apply_smul_I`); $\omega$ is the
    imaginary part of the Hermitian product of
    `g.complexInnerProductSpace hI`
    (`im_inner_eq_compatibleForm_ofComplexModule`, from Tau Ceti's
    `Bundle.ContMDiffRiemannianMetric.complexInnerProductSpace_inner`;
    conjugate-linear in its first argument, as in Mathlib); and, on the
    trivial bundle with fibre `ι → ℂ` (the line bundle for `ι = Fin 1`) and
    a metric pulled back along `complexToRealEuclidean ι`, that map carries
    it to `stdForm ι` (`compatibleForm_ofComplexModule_trivial`, and
    `compatibleForm_ofComplexModule_constComplexEuclidean` for the constant
    metric `Bundle.ContMDiffRiemannianMetric.constComplexEuclidean ι`), so the
    conventions agree with *Standard model*.
  - *The circle bundle of a Hermitian line bundle*
    (`Hermitian/CircleBundle.lean`). With the fibre norm of `g` (the local
    `RiemannianBundle V` of `g.toRiemannianMetric`), the circle bundle is the
    subtype `{p : TotalSpace F V // ‖p.snd‖ = 1}`, used throughout: it is
    the type on which Tau Ceti's `sphereBundleChartedSpace` and
    `isManifold_sphereBundle` (`Riemannian/Sphere.lean`, radius `1`) put the
    smooth structure. Tau Ceti's set `TauCeti.sphereBundle F V` has the same
    membership condition (`TauCeti.mem_sphereBundle`, by `Iff.rfl`), and a
    lemma of `Topology/VectorBundle/SphereBundle/` is used through the
    homeomorphism `Homeomorph.setCongr` that this gives; no second circle
    bundle type is introduced. Its principal-bundle form is Tau Ceti's
    rank-one unitary frame bundle `OrthonormalFrameBundle.Fiber ℂ F V ℂ`,
    whose fibre at `x` is `ℂ ≃ₗᵢ[ℂ] V x` for the inner product
    `g.complexInnerProductSpace hI`, and which
    `OrthonormalFrameBundle.instPrincipalBundleFiber` makes a principal
    bundle for `unitary (ℂ →L[ℂ] ℂ)`. The file states its results for fibres
    with their own complex inner products, which the setting of `g` and
    `hI` supplies by local instances (the part's design says how). It
    gives: the homeomorphism from the total space of that bundle to the
    subtype, sending a frame `φ` to `φ 1`, which turns the right action of
    `unitary (ℂ →L[ℂ] ℂ)` on each fibre, read through
    `Unitary.continuousLinearMapCircleEquiv` (the case `𝕜 = ℂ` of the
    isomorphism below composed with Tau Ceti's `circleEquivUnitary`, in that
    isomorphism's file), into the action of `Circle` on the subtype by
    scalar multiplication in the fibres, free with the fibres as orbits;
    and the `TauCeti.PrincipalBundle Circle` instance on
    `Fiber ℂ F V ℂ` that *First Chern number* asks for, whose trivializations
    are those of `instPrincipalBundleFiber` followed by that isomorphism.
    All of this is topological: the smooth side (smoothness of the action
    and of the coordinate changes, the diffeomorphism onto the submanifold,
    the submersion of the projection) is *First Chern number*'s
    prerequisite 3.
    The isomorphism of `unitary (𝕜 →L[𝕜] 𝕜)` with `unitary 𝕜` involves no
    bundle and holds for every `RCLike 𝕜`, so it has a file of its own,
    `Analysis/CStarAlgebra/Unitary/ContinuousLinearMap.lean`. As a group
    isomorphism it is already in Tau Ceti
    (`Analysis/InnerProductSpace/StrongUnitary/Basic.lean`): the inverse of
    `TauCeti.StrongUnitary.unitaryEquivStrongUnitary 𝕜`
    (`unitary 𝕜 ≃ₜ* StrongUnitary 𝕜 𝕜`, `α ↦ α • 1`, inverse `u ↦ u 1`)
    followed by `TauCeti.StrongUnitary.mulEquivUnitary`
    (`StrongUnitary 𝕜 H ≃* unitary (H →L[𝕜] H)`, the identity on the
    underlying maps). Tau Ceti's topology there is the strong operator
    topology, whereas `OrthonormalFrameBundle` gives `unitary (𝕜 →L[𝕜] 𝕜)`
    the norm topology, so the only new content is continuity for the norm.
    The file defines, in Mathlib's root namespace `Unitary` (it is about
    Mathlib's `unitary`), the `ContinuousMulEquiv`
    `Unitary.continuousLinearMapSelfEquiv 𝕜 : unitary (𝕜 →L[𝕜] 𝕜) ≃ₜ* unitary 𝕜`,
    whose `MulEquiv` is by definition
    `((unitaryEquivStrongUnitary 𝕜).toMulEquiv.trans
    StrongUnitary.mulEquivUnitary).symm`
    (`Unitary.toMulEquiv_continuousLinearMapSelfEquiv`, by `rfl`), so that
    the library has one identification of this group and not two. Both
    directions are continuous by the arguments of Tau Ceti's proof,
    `continuous_eval_const 1` and `continuous_id.smul continuous_const`.
    Its API: `Unitary.coe_continuousLinearMapSelfEquiv_apply` (the value is
    `(u : 𝕜 →L[𝕜] 𝕜) 1`) and `Unitary.continuousLinearMapSelfEquiv_symm_apply`
    (`α` acts by `x ↦ α * x`), both `@[simp]`.
    The connection forms on the circle bundle and their curvature are
    prerequisites of *First Chern number*, which its design lists.
- **The design file decides:** the details of
  `ContMDiffComplexStructure` and its subtypes; the precise form of the
  section spaces above (which bundle; the cover, which `frameTopology` takes
  as explicit frames rather than as an instance, so the file fixes once how
  the statements quantify over it); and which surface
  topology the last milestone needs (none of the decomposition of compact
  surfaces with boundary: the route through nowhere-zero sections under
  *Files* replaces it), with an issue for each missing prerequisite.

### 13. First Chern number (needs `design/first-chern-number.md`)

- **Files:** `Topology/VectorBundle/Complex/FirstChernClass.lean` (the
  first Chern class of a complex bundle, as `TauCeti.complexEulerClass` of
  its determinant line, and the first Chern number over a compact oriented
  surface), and in `Geometry/Manifold/VectorBundle/ChernNumber/`:
  `Basic.lean` (the number of a symplectic bundle, through a compatible
  complex structure), `Clutching.lean` (the disc clutching formula, by
  determinants and Maslov indices), `Gluing.lean`, `Axioms.lean`
  (naturality, functoriality, additivity, normalization, uniqueness),
  `ChernWeil.lean`, `EulerNumber.lean` (with
  `TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex`),
  `ClutchingNumber.lean` (comparison with Tau Ceti's
  `TauCeti.clutchingNumber`, `Topology/VectorBundle/Complex/Clutching.lean`),
  `Splitting.lean` (the splitting description through the Maslov index of
  the overlap loop) and `Extension.lean` (the extension lemma for maps from
  the boundary into $\mathrm{Sp}(2n)$). `design/first-chern-number.md` gives
  the details.
- **Builds on:** *Maslov index* (symplectic loops), *Symplectic vector
  bundles*, Tau Ceti's degree of maps (`TauCeti.HomologicalOrientation.degree`),
  surface genus (`TauCeti.surfaceGenus`), integration of top forms
  (`Geometry/Manifold/DeRham/`), clutching numbers and Euler classes of
  complex bundles.
- **Milestones:** *First Chern number of symplectic vector bundles over
  surfaces*, *Chern–Weil formula for circle bundles over surfaces*, *First
  Chern number as an Euler number*.
- The number is defined from `complexEulerClass` of the determinant line;
  the splitting description of the book, the disc clutching formula and
  `clutchingNumber` are theorems, and no decomposition of surfaces is
  needed. The infrastructure that neither library has (determinant lines,
  coordinate discs, boundary degrees on surfaces with boundary, connection
  forms on circle bundles, among others) comes as prerequisite issues
  before the part's own, as the design file lists them.

### 14. Smooth families (needs `design/smooth-families.md`)

The lemma of `auxiliary/smooth-primitives.md`, which Moser stability and
isotopy extension need, and the passage between families over $[0,1]$ and
over `ℝ` of *Manifolds, families and signs*. Neither Mathlib nor Tau Ceti
has either; Tau Ceti's extension across a boundary,
`TauCeti.HalfSpaceExtension`, is either of finite order or, for Seeley's, needs a
complete target and a function on the whole half-space.

- **Files:** `Geometry/Manifold/DeRham/GoodCover/Basic.lean` (finite good
  covers in the auxiliary page's sense: finitely many open sets each of
  whose nonempty finite intersections carries a smooth contraction,
  the form in which the page's formalization notes and [Weil1952]
  use them) and `Geometry/Manifold/DeRham/GoodCover/Compact.lean`
  (their existence on a compact boundaryless manifold, by Weil's
  construction from Mathlib's `exists_embedding_euclidean_of_compact`,
  through `Geometry/Manifold/Immersion/TangentProjection.lean`), and
  `Geometry/Manifold/DeRham/SmoothFamily/` (the statement (★) of the
  auxiliary page, by its induction over the cover, and its consequences:
  a primitive map $P$, linear on exact $k$-forms, with $P\eta_t$ smooth
  in $(t,x)$ whenever $\eta_t$ is, and, for closed $z_t$ smooth in
  $(t,x)$, coordinates of $[z_t]$ that are smooth in $t$ in a basis
  of Tau Ceti's `TauCeti.deRhamCohomology`; with smooth families of
  forms in `Geometry/Manifold/DifferentialForm/SmoothFamily/`,
  restricted between open subsets with
  `Geometry/Manifold/LocalDiffeomorph/OpenSubset.lean`,
  and the homotopy operator on smooth forms in
  `Geometry/Manifold/DifferentialForm/HomotopyOperator.lean`),
  `Geometry/Manifold/ContMDiff/TimeExtension.lean` and
  `Geometry/Manifold/DifferentialForm/TimeExtension.lean` (Seeley's extension
  in the time variable, from `Analysis/Calculus/ContDiff/Seeley/`, with
  `Analysis/Calculus/ContDiff/FTaylorSeries.lean`,
  `Analysis/Normed/Group/FunctionSeries.lean` and
  `Analysis/Sobolev/Trace/Reflection/HalfSpace.lean`:
  a smooth map, and a smooth form, on `unitInterval × M` is
  the restriction of one on `ℝ × M`, chosen linearly), and
  `Geometry/Diffeomorphism/Diffeotopy/Real.lean` (the bridge: an
  isotopy `ψ : ℝ → M ≃ₘ⟮I, I⟯ M` over `ℝ` restricts to a
  `TauCeti.Diffeotopy I ∞ M`, its inverse being smooth by the inverse
  function theorem, by Tau Ceti's `Diffeomorph.contMDiff_symm_family`; how its `TauCeti.eulerianField` reads in the velocity
  along the motion that `TauCeti.Diffeotopy.HasHamiltonian` uses; and how the
  restriction compares with `TauCeti.timeDependentFlowDiffeotopy`, whose
  family over `ℝ` is jointly smooth by
  `Geometry/Manifold/Flow/TimeDependent.lean`; and the
  reading of a `Diffeotopy` $\Phi$ over `ℝ` as $t\mapsto\Phi_{s(t)}$,
  $s=$ `Real.smoothTransition`, with its `TauCeti.eulerianField`
  $s'(t)X_{s(t)}$, with `Analysis/SpecialFunctions/SmoothTransition.lean`
  and `Geometry/Manifold/SmoothTransition.lean`)
  and `Geometry/Diffeomorphism/Diffeotopy/OfContMDiff.lean` (the
  constructor of a `TauCeti.Diffeotopy I ∞ M` from a jointly smooth map on
  `unitInterval × M` that is the identity at time $0$ and whose slices
  are diffeomorphisms, Tau Ceti having none, its inverse being smooth
  by the inverse function theorem in charts, at every time, after
  extending the map in time by Seeley's extension).  (★)
  is for families over $[0,1]$, forms on `unitInterval × M`, so that the
  primitives it gives extend past both ends by
  `DifferentialForm/TimeExtension.lean`. The
  parametric Poincaré lemma on a member of the cover is Tau Ceti's
  homotopy operator `TauCeti.homotopyOperator` on the cylinder, applied
  as the page's formalization notes say.
- **Builds on:** Mathlib, Tau Ceti (homotopy operators, partitions of unity,
  extension by zero, de Rham cohomology, diffeotopies, the inverse function
  theorem); `Diffeotopy/Real.lean` imports the merged
  `Diffeotopy/Velocity.lean` of *Hamiltonian flows*, for
  `TauCeti.Diffeotopy.mfderiv_cylinderMap_time`.
- **Milestones:** *Smooth families of primitives*, the milestone of the
  auxiliary page. It is not one of the milestones that #94 lists, but Moser
  stability uses it.
- **The design file decides:** the exact form of (★) for forms on
  `unitInterval × M`, the form of the time extension (for maps into a
  normed space, then for forms through their slices),
  how the contractions of a good cover are stated, and whether the induction
  is over Tau Ceti's `TauCeti.mayerVietoris_induction` or a direct strong
  induction.

### 15. Hamiltonian flows (needs `design/hamiltonian-flows.md`)

- **Files:** `Geometry/Diffeomorphism/Diffeotopy/Velocity.lean` (the
  velocity $X_t$ of a `TauCeti.Diffeotopy`, read along the motion, as
  `TauCeti.Diffeotopy.velocity`), with
  `Geometry/Manifold/Instances/Icc.lean` (the unit vector field of an
  interval is smooth), `Geometry/Manifold/MFDeriv/Prod.lean` (the
  derivative of a map on a product on `(0, w)` and `(v, 0)` is a partial
  derivative),
  `Geometry/Diffeomorphism/Diffeotopy/Basic.lean` (facts about diffeotopies
  of any smoothness, used by `Flux/Hamiltonian.lean`),
  `Geometry/Symplectic/Hamiltonian/SymplecticIsotopy.lean`
  (symplectic vector fields and their local flows; a `TauCeti.Diffeotopy`
  has all its slices in `TauCeti.SmoothForm.diffeomorphStabilizer ω`
  exactly when $\iota_{X_t}\omega$ is closed for every $t\in[0,1]$, through
  the reading over `ℝ` by `Real.smoothTransition` in `Diffeotopy/Real.lean` of
  *Smooth families*; the bracket of two symplectic fields is Hamiltonian,
  with the book's bracket written as `-mlieBracket`), from Tau Ceti's
  `TauCeti.forall_mpullback_eq_iff_forall_mextDeriv_interior_eulerianField_eq_zero`,
  `TauCeti.SmoothTwoForm.mem_symplecticVectorFields_iff_mlieDerivForm_eq_zero`
  and `TauCeti.SmoothTwoForm.isHamiltonianVectorField_mlieBracket`;
  `Geometry/Symplectic/Hamiltonian/PoissonAlgebra.lean` (the Leibniz rule,
  which with Tau Ceti's Lie structure `TauCeti.SmoothTwoForm.PoissonLieAlgebra`
  makes $C^\infty(M)$ a Poisson algebra; the energy identity of a
  time-dependent Hamiltonian along `TauCeti.timeDependentFlowOf`; naturality
  $X_{H\circ\chi}=\chi^*X_H$ for a symplectomorphism; the kernel of
  $H\mapsto X_H$ and, for connected $M$, $C^\infty(M)/\mathbb{R}$ as the Lie
  algebra of Hamiltonian fields, from
  `TauCeti.SmoothTwoForm.mem_ker_negHamiltonianLieHom_iff` and
  `range_negHamiltonianLieHom`);
  `Geometry/Symplectic/Flux/Hamiltonian.lean` (named like Tau Ceti's file,
  which has the Hamiltonian isotopies `TauCeti.Diffeotopy.IsHamiltonian`
  and `HasHamiltonian`, with the page's sign $\iota_{X_H}\omega=dH$, their
  composites, inverses and conjugates `HasHamiltonian.trans`, `.symm`
  and `.transDiffeomorph`, and the group
  `TauCeti.SmoothForm.hamiltonianGroup`, normal in
  `diffeomorphStabilizer` by
  `normal_hamiltonianGroup_subgroupOf_diffeomorphStabilizer`. The library
  adds what is missing, in Tau Ceti's namespaces: a diffeotopy of slices in
  the stabilizer is Hamiltonian exactly when each $\iota_{X_t}\omega$ is
  exact, with a smooth Hamiltonian built from Tau Ceti's smooth families of
  primitives on each connected component (the
  primitive of a smooth family of exact one-forms being a public lemma on
  any manifold, in the namespace `SymplecticGeometry` and the file
  `Geometry/Manifold/DeRham/FamilyPrimitive.lean`, which *Isotopy
  extension* applies on open subsets); and uniqueness of the Hamiltonian up
  to a function of time on each component), and
  `Geometry/Symplectic/Flux/CompactSupport.lean` (Hamiltonian diffeotopies
  generated by Hamiltonians that vanish off a fixed compact set, the
  subgroup $\mathrm{Ham}_c$ of their time-one maps, normal in `diffeomorphStabilizer`, and
  $\mathrm{Ham}_c=$ `hamiltonianGroup` on a compact $M$). The folder of
  these two is Tau Ceti's `Geometry/Symplectic/Flux/`, since a folder
  `Flux/Hamiltonian/` beside Tau Ceti's file would keep the two trees from
  moving upstream unchanged.
- **Builds on:** *Smooth families* (only `Diffeotopy/Real.lean`, for
  `SymplecticIsotopy.lean`, `ContMDiff/TimeExtension.lean`, for
  `Flux/CompactSupport.lean`, and the merged `DeRham/GoodCover/Basic.lean`
  and `DifferentialForm/SmoothFamily/Basic.lean`, for
  `DeRham/FamilyPrimitive.lean`); *Contact geometry* (only
  `Geometry/Manifold/DifferentialForm/Flow/Family.lean`, which is merged, for
  `PoissonAlgebra.lean`); Mathlib, Tau Ceti (Hamiltonian vector fields,
  Poisson brackets, Eulerian fields, time-dependent flows and their
  completeness criteria
  `TauCeti.isCompleteVectorField_of_isCompact_of_eq_zero_off`, diffeotopies
  and their Hamiltonians, homotopy operators on cylinders).
- **Milestones:** *Symplectic vector fields and isotopy generators*,
  *Hamiltonian flows and the Poisson algebra*, *Hamiltonian isotopies and
  their composition*. The last is stated with
  `TauCeti.Diffeotopy.IsHamiltonian`, `TauCeti.SmoothForm.hamiltonianGroup`
  and `TauCeti.SmoothForm.diffeomorphStabilizer`. The first and the last
  apply to every jointly smooth family of diffeomorphisms over $[0,1]$
  starting at the identity, through the constructor of `Diffeotopy/OfContMDiff.lean`.
- **The design file decides:** how the velocity $X_t$ of a diffeotopy is
  read (through the bridge to `TauCeti.eulerianField`, or along the motion
  as `HasHamiltonian` reads it), and how $\mathrm{Ham}_c$ is stated beside
  `hamiltonianGroup`.

### 16. Cotangent bundles

- **Files:** in `Geometry/Symplectic/Cotangent/Bundle/`, beside Tau Ceti's
  files there: `Liouville.lean` (named like Tau Ceti's file: uniqueness of
  $\lambda_{\mathrm{can}}$ among one-forms with $\sigma^*\lambda=\sigma$ for
  every one-form $\sigma$, testing against one-forms whose value and
  derivative at a point are chosen freely), `ZeroSection.lean` (along the zero section,
  $\omega_{\mathrm{can}}((v,a),(w,b))=b(v)-a(w)$ in the splitting
  `TauCeti.Bundle.zeroSectionTangentEquiv`), `Lift.lean` (named like Tau
  Ceti's file: for a vector field $Y$, lifting its local flow to $T^*L$ gives
  the flow of $X_H$ for $H(q,p)=p(Y_q)$ where defined, and a complete flow
  when $Y$ is complete); `Geometry/Manifold/Flow/Basic.lean` (named like Tau
  Ceti's file: the differentials of the time-$t$ and time-$(-t)$ maps of a
  maximal flow are inverse, which `Lift.lean` uses);
  `Geometry/Symplectic/Hamiltonian/Manifold.lean` (named like Tau Ceti's
  file: Hamiltonian vector fields of $C^{n+1}$ functions are $C^n$, which
  `Lift.lean` uses); and
  `Geometry/Manifold/VectorBundle/Section/Extension.lean` (named like Tau
  Ceti's file, whose `FiberBundle.contMDiffExtend` it uses: the differential
  of a section in the chart at its value, `Bundle.mfderiv_section_apply`, and
  smooth sections of any smooth vector bundle with a given value and a
  derivative $u\mapsto\xi(u)\,b$ at a point,
  `ContMDiffSection.exists_mfderiv_eq`, which `Liouville.lean` tests
  against).
- **Builds on:** Tau Ceti: `TauCeti.CotangentBundle.liouvilleForm` with
  `mpullback_liouvilleForm`, `symplecticForm` (which is
  $-d\lambda_{\mathrm{can}}$, the page's sign) with `inChartAt_symplecticForm_apply`,
  `Diffeomorph.mpullback_cotangent_liouvilleForm` and
  `Diffeomorph.mpullback_cotangent_symplecticForm` (lifts preserve both
  forms), and `Diffeomorph.existsUnique_cotangent_eq_of_mpullback_liouvilleForm`
  (the converse). The lifted-flow statement is proved for the local flow
  directly; Tau Ceti's `TauCeti.CotangentBundle.momentMap_apply` covers only
  group actions.
- **Milestones:** *Canonical cotangent structure and cotangent lifts*. The
  part states it as one theorem, citing the existing parts.

### 17. Moser isotopy (needs `design/moser-isotopy.md`)

- **Files:** `Geometry/Symplectic/Moser/Stability.lean` (Moser stability for
  a smooth family over $[0,1]$, a form on `unitInterval × M`, of
  cohomologous symplectic forms on a closed manifold, with a
  `TauCeti.Diffeotopy` as the isotopy: (★) of *Smooth families* gives a
  family $\beta_t$ over $[0,1]$ with $\omega_t=\omega_0+d\beta_t$; its
  extension over `ℝ` gives forms $\omega_0+d\beta_t$ that are cohomologous
  for every $t$ and, $M$ being compact, symplectic for $t$ in some
  $(-\varepsilon,1+\varepsilon)$; after a reparametrization that is the
  identity on $[0,1]$, Tau Ceti's
  `TauCeti.SmoothTwoForm.exists_isotopy_mpullback_eq` applies, and
  `Diffeotopy/Real.lean` restricts its isotopy to a `Diffeotopy`),
  `Geometry/Symplectic/Moser/Relative.lean` (the relative theorem with
  prescribed first derivative along an embedded, not necessarily compact
  or properly embedded, submanifold: Tau Ceti's
  `TauCeti.SmoothTwoForm.exists_diffeomorph_opens_of_eq_along` is the compact
  case; the non-compact case uses Tau Ceti's tubular neighbourhoods of
  variable radius, `Geometry/Manifold/TubularNeighborhood/`, the relative
  Poincaré primitive with zero first jet of
  `Geometry/Manifold/DifferentialForm/Relative/FirstJet.lean`, and the domain
  of the Moser flow up to time one), `Geometry/Symplectic/Moser/Field.lean`
  (the cut-off Moser field of a family of two-forms, the segment
  $\omega_0+t(\omega_1-\omega_0)$ among them), `Geometry/Symplectic/Moser/Isotopy.lean`
  (the isotopy of embeddings fixing a compact submanifold, with Tau Ceti's
  relative Poincaré primitive, which vanishes as a full covector, in place
  of the correction by $dF$; the trajectory argument is that of
  `Moser/Family.lean` of *Isotopy extension*, for the segment), and
  `Geometry/Symplectic/Manifold/Darboux.lean` (named
  like Tau Ceti's file: Darboux charts with a prescribed derivative at the
  centre, for any linear symplectic form on the target, from Tau Ceti's
  Darboux charts followed by a linear symplectomorphism; and that transition
  maps of such charts have symplectic derivatives), with lemmas on
  nondegenerate two-forms in
  `Geometry/Symplectic/Manifold/Family.lean` and `Flat.lean`, and the chain
  rule for transitions that `Darboux.lean` uses, in
  `Geometry/Manifold/LocalDiffeomorph/MFDeriv.lean`, and the bilinear forms
  of sums, multiples and differences of smooth two-forms in
  `Geometry/Manifold/DifferentialForm/Smooth.lean`, and the primitive on a
  tube of a difference of closed forms in
  `Geometry/Manifold/TubularNeighborhood/RelativePoincare.lean`, named like
  Tau Ceti's files. The folder is `Geometry/Symplectic/Moser/`, because
  Tau Ceti has the files `Geometry/Symplectic/Manifold/Moser.lean` and
  `RelativeMoser.lean`, beside which this library may not have folders of
  those names.
- **Builds on:** *Smooth families* (only `Stability.lean`); *Isotopy extension*
  (only `Isotopy.lean`, through `Moser/Family.lean`);
  Tau Ceti (Moser's theorem with given primitives, the compact relative
  theorem, tubular neighbourhoods and relative primitives, Darboux charts
  `TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart_of_symplecticForm`).
- **Milestones:** *Moser stability*, *Relative Moser theorem with prescribed
  first derivative*, *Darboux theorem with prescribed derivative*, *Relative
  Moser theorem fixing a submanifold*.
- **The design file decides:** the statement of "cohomologous" (exactness of
  $\omega_t-\omega_0$ for each $t$, with Tau Ceti's exact forms), how the
  isotopy of embeddings of `Isotopy.lean`, a `TauCeti.SmoothIsotopy` of a
  neighbourhood, is obtained from the Moser flow, and the variable-radius
  construction for non-compact submanifolds, which *Symplectic
  neighbourhoods* reuses.

### 18. Isotopy extension (needs `design/isotopy-extension.md`)

- **Files:** in `Geometry/Symplectic/IsotopyExtension/`: `Velocity.lean`
  (velocity forms of symplectic families of embeddings), `Flow.lean`
  (extension of such a family by an ambient symplectic or Hamiltonian flow),
  `Ball/Basic.lean` and `Ball/Isotopy.lean` (symplectic ball extension, on
  closed balls of `StdSpace (Fin n)` with `stdForm`, as *Conventions* asks
  of metric statements; the case of radius $0$ through smooth symplectic
  frames along the path of centres),
  `Cohomological/Primitive.lean` and `Cohomological/Basic.lean` (extension of
  a family of symplectic embeddings of a neighbourhood of a compact
  neighbourhood deformation retract $Q$ when $H^1(M)\to H^1(Q)$ is onto,
  Hamiltonian when $H^1(Q)=0$, with $H^1(Q)$ read through the periods on
  $H_1(Q;\mathbb{Z})$), and `Submanifold.lean` (neighbourhood extension of
  isotopies of a compact submanifold, by isotopy extension and Moser's
  argument along the family); and the general files
  `Geometry/Symplectic/Moser/Family.lean` (Moser's argument near a compact
  set along a family and with a parameter, beside *Moser isotopy*'s files),
  `Geometry/Manifold/SmoothIsotopy/Extension.lean` (named like Tau Ceti's
  file: isotopy extension at every time, without Tau Ceti's change of time),
  `Geometry/Manifold/SmoothEmbedding/Neighborhood.lean`,
  `AlgebraicTopology/Singular/NDRPair.lean` (singular homology near the
  subset of Tau Ceti's NDR pairs) and
  `Analysis/Matrix/SymplecticGroup/Connected.lean` (named like Tau Ceti's
  file: smooth paths in $\mathrm{Sp}(2n)$), as the design file gives them.
- **Builds on:** *Hamiltonian flows* (only `DeRham/FamilyPrimitive.lean`,
  `Flux/Hamiltonian.lean` and `Flux/CompactSupport.lean`: the primitives of a
  family of exact one-forms, and the diffeotopy of a compactly supported Hamiltonian), *Smooth families*
  (only `ContMDiff/TimeExtension.lean`, `DifferentialForm/TimeExtension.lean`,
  and finite-dimensional de Rham cohomology from
  `DeRham/SmoothFamily/GoodCover.lean`), *Moser isotopy* (only `Moser/Field.lean`, the
  cut-off Moser field, taken for a family of two-forms), the
  merged *Standard model* and *Linear Moser*; Tau Ceti's smooth isotopy
  extension `TauCeti.SmoothIsotopy.exists_diffeotopy_apply_eq` and ambient
  velocity fields, relative primitives, tubular neighbourhoods and periods
  on singular homology.
- **Milestones:** *Symplectic ball extension*, *Symplectic isotopy
  extension*, *Neighbourhood extension of submanifold isotopies*.
- **The design file decides:** how a symplectic embedding of a closed ball is
  stated (on an open neighbourhood of the ball, or on the ball as a manifold
  with boundary), and how $H^1(Q;\mathbb{R})$ of a compact subset is read
  (de Rham cohomology does not apply to a subset; for instance through
  neighbourhoods that retract onto $Q$, or a cohomology theory that Tau Ceti
  or Mathlib has), with a proposed issue for any missing prerequisite.

### 19. Symplectic neighbourhoods (needs `design/symplectic-neighbourhoods.md`)

- **Files:** `Geometry/Symplectic/Manifold/CharacteristicFoliation.lean`
  (for a closed two-form of constant rank, foliation-compatible submersions
  onto a ball with connected fibres near every point, and the unique
  symplectic form they descend to; the coisotropic case, with kernel
  $(TQ)^\omega$ and isotropic leaves; from Tau Ceti's
  `TauCeti.SmoothForm.characteristicFoliation`,
  `TauCeti.IsInvolutiveDistribution.exists_flatChart`,
  `TauCeti.RoughForm.descendedForm` and
  `TauCeti.SmoothTwoForm.isSymplectic_descendedForm_iff`, and the closed-form lemmas of
  `Analysis/Calculus/DifferentialForm/LieDeriv.lean`), and in
  `Geometry/Symplectic/Neighborhood/`: `Extension.lean` (along the
  submanifold, a smooth family of linear symplectomorphisms built from
  compatible complex structures by the formula of
  `LinearAlgebra/Symplectic/Extension.lean`, whose adjoint step is smooth by
  `Geometry/Manifold/VectorBundle/Adjoint.lean`), `Tubular.lean` (the common step of
  the four theorems: given a diffeomorphism between two embedded
  submanifolds and, over it, a bundle map $TM_0|_{Q_0}\to TM_1|_{Q_1}$ that
  is a linear symplectomorphism on each fibre, some diffeomorphism of
  neighbourhoods has that bundle map as its derivative along $Q_0$, proved
  without symplectic forms in `Geometry/Manifold/TubularNeighborhood/MFDeriv.lean`,
  which *Moser isotopy*'s relative theorem
  then corrects to a symplectomorphism with the same first jet),
  `Basic.lean` (the comparison theorem for submanifolds whose restricted
  form has constant rank, from the two files before it, of which the four
  theorems are corollaries), `Symplectic.lean`, `Lagrangian.lean` (the
  model $T^*L$ with $-d\lambda_{\mathrm{can}}$, along the zero section of
  `Geometry/Manifold/VectorBundle/ZeroSection.lean`, a smooth embedding),
  `Isotropic.lean` (with the
  symplectic normal bundle $(TQ)^\omega/TQ$, read fibrewise by
  *Symplectic vector spaces*' linear reduction), `Coisotropic.lean` and
  `AdaptedDarboux.lean` (Darboux charts adapted to the four types, from a
  chart of the submanifold suited to its type and Tau Ceti's pointwise
  relative Darboux theorem), with the general
  `Geometry/Manifold/LocalDiffeomorph/Extend.lean` (an immersion extended to a local
  diffeomorphism, and centred charts) and
  `LinearAlgebra/FiniteDimensional/Extension.lean` (an injective linear map
  extended to a linear equivalence),
  `Geometry/Manifold/DifferentialForm/Pullback/LocalDiffeomorph.lean` (pull-back
  along the local inverse of a local diffeomorphism),
  `Geometry/Manifold/LocalDiffeomorph/Basic.lean` (a local
  diffeomorphism on the target of its local inverse, shared with *Smooth
  families*) and
  `Topology/Maps/Embedding.lean` (an inducing map cut out by a chart).
  The symplectic normal bundle of a symplectic submanifold is Tau Ceti's
  normal bundle with `TauCeti.SmoothEmbedding.symplecticNormalForm`; the
  symplectic normal bundle $(TQ)^\omega/TQ$ of an isotropic one is given by
  smooth lifts of its maps (see the design file).
- **Builds on:** *Moser isotopy* (`Relative.lean`, only for `Tubular.lean` and
  what follows it), *Symplectic
  vector spaces* (`Reduction.lean` and `Subspace.lean`, merged), *Compatible
  complex structures* (`LinearAlgebra/Symplectic/Compatible.lean` and
  `Topology/Algebra/Module/BilinearForm.lean`, merged), Tau Ceti (tubular
  neighbourhoods, the normal bundles of Lagrangian and symplectic embeddings,
  compatible almost complex structures, relative Darboux, `TauCeti.exists_partialDiffeomorph_fix_immersion_compContinuousLinearMap_fderiv_eq`).
  `CharacteristicFoliation.lean` uses only Tau Ceti and `LieDeriv.lean` and can
  start at once.
- **Unmerged work of #3 it may wait for.** The linear extensions in the
  proofs choose complements: Lagrangian complements of a Lagrangian or
  isotropic tangent bundle, and a symplectic trivialization of the normal
  bundle for adapted charts. If the design file takes them from compatible
  complex structures on a symplectic bundle, the issues that do wait for
  #254 (existence of compatible pairs); if it states the isomorphism
  $\Phi$ of the symplectic neighbourhood theorem as an isomorphism with a
  pull-back bundle, for #269 (pull-backs); if the adapted charts use local
  Darboux frames of a bundle, for #266. Otherwise the part waits for no
  open issue of #3. The design file chooses compatible complex structures,
  and takes them from Tau Ceti's
  `TauCeti.SmoothTwoForm.IsNondegenerate.exists_compatible`, so the part
  waits for none of #254, #266 and #269.
- **Milestones:** *Characteristic foliations and local symplectic
  quotients*, *Symplectic neighbourhood theorem*, *Lagrangian neighbourhood
  theorem*, *Isotropic neighbourhood theorem*, *Coisotropic neighbourhood
  theorem*, *Darboux charts adapted to submanifolds*.
- The general model $K^*\oplus E$ of the page's section on explicit
  neighbourhood models, with a connection on $E$, is not built: no milestone
  needs it, since the neighbourhood theorems go through `Tubular.lean` and
  the adapted charts through local pieces, where the models are flat.

### 20. Contact geometry (needs `design/contact-geometry.md`)

- **Files:** in `Geometry/Contact/`, beside Tau Ceti's files there:
  `Hamiltonian.lean` (named like Tau Ceti's file: the bijection between
  contact vector fields and functions as one equivalence; the rescaling
  formula $\phi_t^*\alpha=\exp(\int_0^tR(H_s)\circ\phi_s\,ds)\,\alpha$ of the
  flow, over `ℝ` on the flow's domain, from Tau Ceti's
  `TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_mem`;
  contact fields as the fields whose local flows preserve $\xi$; $X_H$ is
  transverse to $\xi$ exactly where $H\neq0$, and then the Reeb field of
  $\alpha/H$, with the same coorientation exactly when $H>0$),
  `Darboux/Strict.lean` (named like Tau Ceti's file: the page's normal form
  $\sum_ip_i\,dq_i-dz$ at a point, with Reeb field $-\partial_z$, from Tau
  Ceti's `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart_of_finrank_eq`
  by the change of coordinates of *Manifolds, families and signs*),
  `Levi.lean` and `Moser.lean` (named like Tau Ceti's files: kernels of
  local one-forms as smooth hyperplane fields, and the change-of-form law
  of the contact-Moser vector at one point, both used by `Family.lean`, and
  the contact-Moser vector under pullback and restriction to open subsets,
  which `Gray.lean` uses for the Gray vector),
  `Family.lean` (named like Tau Ceti's file: `IsContactFamily`, smooth
  families over $[0,1]$ of contact structures that need not be
  coorientable, and their local defining forms over `ℝ`, through the time
  extension), `Gray.lean` (named like Tau Ceti's file: Gray stability for a family over
  $[0,1]$, with the normalization $X_t\in\xi_t$ and its uniqueness, for
  families of contact structures that need not be coorientable, and the
  rescaling for global forms; from Tau Ceti's `TauCeti.SmoothForm.grayDiffeomorph`
  and `TauCeti.SmoothForm.eq_grayVectorField_iff`, whose families are over
  `ℝ`, through the time extension, the reparametrization that is the
  identity on $[0,1]$, and `Diffeotopy/Real.lean` of *Smooth families*), and `LegendrianNeighborhood.lean` (the Legendrian neighbourhood
  theorem for an embedded Legendrian $L$, properness not being needed, with model the form
  $\lambda_{\mathrm{can}}-dz$ near $L\times\{0\}$ in $T^*L\times\mathbb{R}$:
  a hypersurface through $L$ transverse to the Reeb field, the Lagrangian
  neighbourhood theorem there, a relative primitive from Tau Ceti's
  `TauCeti.SmoothEmbedding.exists_isSmoothForm_relative_primitive`, and the
  Reeb flow, with the openness of immersions transverse to a vector field
  from `Geometry/Manifold/Immersion/Transverse.lean`, which imports
  `Topology/Algebra/Module/ContinuousLinearMap/PiProd.lean` (itself importing
  `LinearAlgebra/Prod.lean`), and a smooth injective
  map of the normal bundle from
  `Geometry/Manifold/TubularNeighborhood/Riemannian/Injective.lean`); and
  `Geometry/Manifold/DifferentialForm/Flow/Family.lean`
  (named like Tau Ceti's file: Moser's principle along one trajectory, in
  the rescaling case, which `Gray.lean` uses, the preservation of a
  closed form with closed contractions by a local time-dependent flow, which
  `PoissonAlgebra.lean` of *Hamiltonian flows* uses, and the slices of
  pullbacks along `Prod.map id f`), and, named like Tau Ceti's files,
  `Geometry/Manifold/DifferentialForm/LieDeriv.lean` (the Lie derivative of
  forms on a manifold is linear in the field, from flat lemmas that this part adds to
  `Analysis/Calculus/DifferentialForm/LieDeriv.lean`) and
  `Geometry/Manifold/DifferentialForm/DegreeOne.lean` (a smooth one-form on a
  smooth field is smooth), which `Hamiltonian.lean` uses, and `Standard.lean`
  and `Pullback.lean` (both named like Tau Ceti's files: the Reeb field of the
  standard form, and the transport of Reeb vectors by a local pullback, which
  `Darboux/Strict.lean` uses, as it uses
  `PartialDiffeomorph.mvfderiv_trans_toDiffeomorph` from
  `Geometry/Manifold/LocalDiffeomorph/MFDeriv.lean`).
- **Builds on:** Tau Ceti (contact forms, Reeb fields, contact Hamiltonians,
  strict and distribution Darboux charts, Gray's theorem for families over
  `ℝ`); `Family.lean` and `Gray.lean` also on *Smooth families*
  (`ContMDiff/TimeExtension.lean`, `DifferentialForm/TimeExtension.lean`,
  `Diffeotopy/Real.lean`); `LegendrianNeighborhood.lean` also on *Symplectic
  neighbourhoods* (`Lagrangian.lean`); `Darboux/Strict.lean` also on
  *Moser isotopy* (`LocalDiffeomorph/MFDeriv.lean`, merged). The other
  files can start at once.
- **Milestones:** *Contact vector fields and contact Hamiltonians*, *Contact
  Darboux theorem*, *Gray stability*, *Legendrian neighbourhood theorem*.
- **The design file decides:** how a smooth family of contact structures
  that are not coorientable is represented (for instance as a family of
  hyperplane distributions locally the kernels of smooth families of contact
  forms, beside Tau Ceti's `TauCeti.IsContactDistribution`).

### 21. Liouville structures (needs `design/liouville-structures.md`)

- **Files:** `Geometry/Symplectic/Liouville/ContactType.lean` (named like Tau
  Ceti's file: for an embedded hypersurface, a contact form $\alpha$
  with $d\alpha=-i^*\omega$ exists exactly when a transverse Liouville field
  exists near it; for a prescribed $\alpha$ a Liouville field inducing it.
  Tau Ceti has the
  direction from a Liouville field, `TauCeti.IsContactType.isContactForm_mpullback`;
  the converse comes from a relative
  primitive), `Geometry/Symplectic/Liouville/Collar.lean` (named like Tau
  Ceti's file: the collar of such a hypersurface, with
  $\Phi^*\omega=-d(e^s\alpha)$ on a neighbourhood of $\{0\}\times Q$, of
  uniform width when $Q$ is compact, from Tau Ceti's collars for a given
  field, `TauCeti.mpullback_flowOf_comp_apply_eq_symplectization`,
  `TauCeti.exists_continuous_pos_injOn_flowOf_comp` and
  `TauCeti.exists_pos_injOn_flowOf_comp`), `Geometry/Contact/StableHamiltonian.lean` (named like Tau
  Ceti's file: Tau Ceti's `TauCeti.SmoothForm.IsStableHamiltonian α ω`, with
  $(\Omega,\lambda)=(\omega,\alpha)$, and its Reeb field
  `TauCeti.SmoothForm.characteristicVectorField`; the library adds the
  equivalence of its pointwise condition with $\lambda\wedge\Omega^{n-1}\neq0$
  in dimension $2n-1$, the invariance of both forms under the Reeb flow, the
  model $\Omega-d(r\lambda)$ on $(-\varepsilon,\varepsilon)\times M$ for a
  compact $M$, the contact case, and the converse normal form, by Tau Ceti's
  compact relative Moser theorem along $\{0\}\times M$),
  `Topology/Sets/Strip.lean` (the open strip
  $(-\varepsilon,\varepsilon)\times X$ of $\mathbb R\times X$ and the tube
  lemma for it),
  `Geometry/Manifold/Boundary/Collar/Flow/Local.lean` and
  `Geometry/Manifold/Boundary/Collar/Flow/Basic.lean` (the smooth collar of
  a compact boundary whose normal lines are the integral curves of a given
  outward field),
  `Geometry/Symplectic/Liouville/Filling.lean` (strong fillings: compact
  symplectic manifolds with boundary with an outward Liouville field near
  the boundary, and their Liouville collar),
  `Geometry/Manifold/Boundary/Collar/End.lean` (attaching the end
  $[0,\infty)\times\partial W$ to a manifold with boundary along a smooth
  collar, with Tau Ceti's `Geometry/Manifold/Gluing/`), `Geometry/Symplectic/Liouville/Completion.lean` (named
  like Tau Ceti's file: the completion $\widehat W$, glued from the interior
  of $W$ and $(-\varepsilon,\infty)\times\partial W$ along the Liouville
  collar by `End.lean`,
  with its form, its Liouville field $\partial_s$ on the end, and the
  extension of the primitive of a Liouville domain), and
  `Geometry/Symplectic/Liouville/Domain.lean` (named like Tau Ceti's file:
  the completion of a Liouville domain is a `TauCeti.IsLiouvilleCompletion`).
- **Builds on:** Tau Ceti (Liouville fields and collars, contact type,
  stable Hamiltonian structures, the compact relative Moser theorem, gluing,
  boundary collars in `Geometry/Manifold/Boundary/Collar/`, the
  boundaryless re-modelling `TauCeti.BoundarylessModel`), the
  library's `Geometry/Manifold/IsManifold/InteriorBoundary.lean` of
  *Symplectic vector bundles* (the interior of a manifold with boundary as a
  boundaryless manifold), which is merged, the library's
  `Geometry/Symplectic/Manifold/Family.lean` of *Moser isotopy* (openness of
  nondegeneracy, for `StableHamiltonian.lean`), which is merged,
  `Geometry/Manifold/DifferentialForm/Smooth.lean` of *Moser isotopy* (for
  `StableHamiltonian.lean`), and *Smooth families*: its
  `Analysis/Calculus/ContDiff/Seeley/Extension.lean`,
  `Geometry/Manifold/LocalDiffeomorph/Basic.lean` and
  `Geometry/Manifold/MFDeriv/Chart.lean`, which are merged, for
  `Collar/Flow/Local.lean`, which extends a field across the boundary, and its
  `DifferentialForm/SmoothFamily/Basic.lean`, which is merged, for
  `StableHamiltonian.lean`. `Completion.lean` uses
  `Filling.lean` and `End.lean`.
- **Milestones:** *Contact-type hypersurfaces and Liouville collars*, *Stable
  Hamiltonian structures and their neighbourhood model*, *Completion of a
  strong filling*.
- **The design file decides:** the representation of a strong filling (a
  manifold with boundary modelled on a half-space, as the page has it,
  rather than Tau Ceti's domains `TauCeti.IsLiouvilleDomain` inside a given
  boundaryless manifold, which presuppose the ambient manifold that the
  completion constructs), the Liouville collar at a boundary, and how the
  completion of a Liouville domain is compared with Tau Ceti's
  `TauCeti.IsLiouvilleCompletion`.

### 22. Almost complex manifolds

- **Files:** `Geometry/Symplectic/Manifold/AlmostComplex/Contractible.lean`
  (the case $E=TM$ of part 12's
  `SymplecticGeometry.Bundle.contractibleSpace_compatible_tames`: through
  `tangentEquiv`, `tangentHomeomorph` and `compatible_tangentEquiv_iff`, the
  subtypes of compatible and of taming structures of
  `TauCeti.SmoothAlmostComplexStructure I M` for a nondegenerate `ω` are
  contractible in Tau Ceti's `frameTopology`; the spaces of compatible and
  of taming forms for a fixed structure, and the homotopy equivalence
  $\omega\mapsto J_{g,\omega}$, are stated on part 12's
  `Bundle.ContMDiffTwoForm I ⊤ EB (TangentSpace I)` with its frame topology,
  since Tau Ceti puts no topology on `SmoothTwoForm`; and the two
  consequences: $M$ has an almost complex structure exactly when it has a
  nondegenerate two-form, and the homotopy equivalence gives a bijection
  between the path components of the two spaces) and
  `Geometry/Symplectic/Manifold/AlmostComplex/Metric.lean` (named like Tau
  Ceti's file: Tau Ceti's `TauCeti.SmoothTwoForm.Compatible.metric`, the
  metric $g_J$ of a compatible pair as a `Bundle.ContMDiffRiemannianMetric`
  on $TM$, with `metric_inner`, is part 12's `Compatible.metric` read
  through `tangentEquiv`; and, for a fixed $J$, the one-to-one correspondence of
  metrics compatible with $J$ and nondegenerate forms compatible with $J$,
  through part 12's `compatibleForm`, with its two evaluation lemmas).
- **Builds on:** *Symplectic vector bundles* (only the merged
  `Symplectic/ComplexStructure/Basic.lean` and `Contractible.lean`, and
  `Geometry/Manifold/VectorBundle/ComplexStructure.lean` for `tangentEquiv`
  and `tangentHomeomorph`); Tau Ceti.
- **Milestones:** *Compatible and tame almost complex structures on
  manifolds*, over a Hausdorff σ-compact manifold, in the compact-open
  $C^\infty$ topology, as part 12 states the bundle milestone. The part needs
  no design file: its statements are those of part 12 on the tangent bundle.

### 23. Nijenhuis tensor

- **Files:** `Geometry/Symplectic/Manifold/Nijenhuis.lean` (named like Tau
  Ceti's file, in Tau Ceti's namespace
  `TauCeti.SmoothAlmostComplexStructure`: $N_J(v,Jv)=0$; naturality,
  `nijenhuis_pullback`, for Tau Ceti's `pullback` along a diffeomorphism,
  from `mfderiv_nijenhuis_of_eventually_related`; and the formula of
  $N_J$ through any torsion-free covariant derivative on $TM$, with the
  milestone as one theorem),
  `Geometry/Symplectic/Manifold/AlmostComplex/Covariant.lean` (the covariant
  derivative $\nabla J$ of an almost complex structure for a covariant
  derivative on $TM$, Tau Ceti's `CovariantDerivative.hom` applied to the
  section `toEndomorphism`, with the differentiability of that section that
  Tau Ceti's `CovariantDerivative.hom_apply_apply_anticomm`,
  $(\nabla_vJ)J=-J(\nabla_vJ)$ for every covariant derivative, the
  derivative of $J^2=-1$, takes; *Almost Kähler geometry* uses both) and
  `Geometry/Manifold/Complex/Integrable.lean`
  (`TauCeti.SmoothAlmostComplexStructure.IsIntegrable J`: every point lies
  in the source of a chart `ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞` on
  whose target Tau Ceti's `chartPushforward` of `J` is a linear structure
  `J₀ : TauCeti.AlmostComplexStructure E`, one for each chart; on a
  manifold with boundary no boundary point has such a chart; with
  `isIntegrable_ofComplexManifold`, from Tau Ceti's
  `MDifferentiableAt.mfderiv_ofComplexManifold_apply`, invariance under
  `pullback`, and
  `IsIntegrable.nijenhuis_eq_zero`, from Mathlib's
  `VectorField.mpullback_mlieBracket` for constant fields pulled back along a
  chart; on surfaces modelled on `𝓘(ℝ, ℂ)`, the
  comparison with Tau Ceti's isothermal charts,
  `isIntegrable_iff_forall_exists_isIsothermalChart`); the lemmas on Tau
  Ceti's `chartPushforward` of a smooth `J` along a smooth chart that
  `Integrable.lean` uses are in
  `Geometry/Symplectic/Manifold/AlmostComplex/Chart.lean`, which imports no
  Nijenhuis material.
- **Builds on:** Mathlib (`mlieBracket`, `CovariantDerivative.torsion`) and
  Tau Ceti (`nijenhuis` and its lemmas, `pullback`, `CovariantDerivative.hom`,
  the eigenbundles of `J`); *Smooth families* (only
  `Geometry/Manifold/LocalDiffeomorph/Basic.lean`, which `Integrable.lean`
  imports for the local inverse of a local diffeomorphism); *Moser isotopy*
  (only `Geometry/Manifold/LocalDiffeomorph/MFDeriv.lean`, merged, which
  `AlmostComplex/Chart.lean` imports for `PartialDiffeomorph.mfderivSymmEquiv`).
- **Milestones:** *Nijenhuis tensor*. Existing parts: part 1 is
  `nijenhuis` (a tensor by construction), `nijenhuis_apply` and
  `nijenhuis_antisymm`; part 2 is `nijenhuis_self`, `nijenhuis_apply_left`,
  `nijenhuis_apply_right` and `nijenhuis_eq_zero_of_finrank_eq_two`; part 4
  on the model is `nijenhuis_const`; part 6 is
  `isInvolutiveComplexDistribution_eigenspace_I_iff`. The part adds parts 3
  and 5, the integrable case of part 4, and the theorem that states all six.
  No design file is needed.

### 24. Isothermal coordinates (needs `design/isothermal-coordinates.md`)

- **Files:** `Geometry/Manifold/Complex/Isothermal.lean` (named like Tau
  Ceti's file: every smooth almost complex structure on a surface modelled
  on `𝓘(ℝ, ℂ)` has smooth isothermal charts, from Tau Ceti's smooth planar
  `TauCeti.Beltrami.exists_centered_smooth_isothermal_chart` read through the
  charts of the surface; hence every almost
  complex structure on a boundaryless manifold of real dimension two, over any
  two-dimensional model, is `IsIntegrable`; and isothermal coordinates for
  a Riemannian metric on an oriented surface, through the structure of
  rotation by a right angle that the metric and the orientation give,
  Mathlib's `Orientation.rightAngleRotation` fibrewise); and, in
  `Analysis/Complex/Beltrami/` beside Tau Ceti's files, planar charts of
  class $C^{k+1}$ for a small $C^{k,\alpha}$ coefficient.
- **Regularity.** Tau Ceti's `Beltrami/Isothermal.lean` gives planar
  isothermal charts of every finite order and smooth ones
  (`TauCeti.Beltrami.exists_isothermal_chart_finite_order`,
  `TauCeti.Beltrami.exists_centered_smooth_isothermal_chart`), so the
  surface charts need no planar regularity from the part.
- **Builds on:** *Nijenhuis tensor* (only `Integrable.lean`); Tau Ceti's
  Beltrami files.
- **Milestones:** *Integrability of almost complex structures on surfaces*.
  It follows the Beltrami route, not the route the page prefers (see
  *Departures*).

### 25. Complex submanifolds

- **Files:** `Geometry/Symplectic/Manifold/AlmostComplex/Submanifold.lean`
  (for a `TauCeti.SmoothEmbedding` $f:N\to M$ whose tangent images are
  $J$-invariant: the restricted structure on $N$, with $df$ complex linear;
  the pull-back of a form taming, or compatible with, $J$ is nondegenerate
  and tames, or is compatible with, the restriction, the form conditions
  being checked on $df_x v$ through `mfderiv_restrict_apply` and
  nondegeneracy following from taming; closedness passes to the pull-back, so $N$ is a
  symplectic submanifold in the sense of Tau Ceti's
  `IsSymplecticSubmanifoldEmbedding`; the Nijenhuis tensor of the
  restriction is the restriction of $N_J$, so `IsKahler` passes to $N$; and
  if $J$ is integrable and $N$ has no boundary, so is the restriction,
  since a complex linear left inverse of the differential of a chart of
  $M$ in which $J$ is constant, composed with that chart and $f$, is a chart
  of $N$ by the inverse function theorem) and
  `Geometry/Manifold/Immersion/TangentEndomorphism.lean` (an endomorphism
  field of $TN$ that $df$ relates to a smooth one along $f$ is smooth, when
  $df$ has left inverses; it gives the restriction its smoothness),
  `Geometry/Manifold/Immersion/Chart.lean` (the derivative of an immersion
  in its normal-form charts) and
  `Geometry/Manifold/VectorField/Immersion.lean` (beside Tau Ceti's file of
  that name: every tangent vector at a point of an immersion is the value
  of a field related near it to a field on the target; it gives the
  Nijenhuis tensor of the restriction).
- **Builds on:** *Nijenhuis tensor* (`Nijenhuis.lean` for naturality along
  embeddings, `Integrable.lean`); *Linear complex structures*
  (`LinearAlgebra/ComplexStructure/Hom.lean`, for complex linear left
  inverses); Tau Ceti.
- **Milestones:** *Complex submanifolds of Kähler manifolds*, except its
  last sentence, on $\mathbb CP^n$, which *Complex projective space* proves.
  No design file is needed.

### 26. Almost Kähler geometry (needs `design/almost-kahler-geometry.md`)

- **Files:** `Geometry/Manifold/VectorBundle/CovariantDerivative/TwoForm.lean`
  (for a covariant derivative without torsion, the exterior derivative of
  a two-form as the cyclic sum of $\nabla\omega$; the analogue for two-forms of Tau Ceti's
  `Geometry/Manifold/VectorBundle/CovariantDerivative/ExteriorDerivative.lean`,
  which treats one-forms, in Mathlib's namespace `CovariantDerivative`),
  `Geometry/Symplectic/Manifold/AlmostComplex/LeviCivita.lean` (for
  $J\in\mathcal J(M,\omega)$ and the Levi-Civita connection of $g_J$: the
  four identities, the fourth for closed $\omega$),
  `LinearAlgebra/ComplexStructure/Trilinear.lean` (the linear algebra
  behind the fourth identity) and
  `Geometry/Symplectic/Manifold/Kahler.lean` (named like Tau Ceti's file:
  the identity expressing $\langle N_J(X,Y),Z\rangle$ through $d\omega$ and
  $\nabla J$, and $\nabla J=0$ if and only if $d\omega=0$ and $N_J=0$, that
  is, for a compatible pair, if and only if it is `IsKahler`).
- **Builds on:** *Almost complex manifolds* (only `Metric.lean`); *Nijenhuis
  tensor* (`Covariant.lean` and the connection formula of `Nijenhuis.lean`);
  Mathlib's Levi-Civita connection.
- **Milestones:** *Levi-Civita derivative of a compatible almost complex
  structure* and *Parallel almost complex structures and the Kähler
  condition*, by the page's first proof and its proof route, with $N_J=0$
  and not integrability in the second. The design file decides how $g_J$ is
  installed as Mathlib's `RiemannianBundle` instance, and in which form
  (vector fields or tangent vectors) the identities are stated.

### 27. Complex projective space (needs `design/complex-projective-space.md`)

- **Files:** `Geometry/Manifold/DifferentialForm/Dolbeault/Potential.lean`
  ($\tfrac i2\partial\bar\partial f$ as a real two-form), and
  `Geometry/Manifold/Projectivization/Hopf.lean`
  (the projection from $\mathbb C^{n+1}\setminus0$, and from the unit
  sphere, to $\mathbb CP^n$ as smooth submersions); in
  `Geometry/Manifold/Projectivization/FubiniStudy/`, beside
  Tau Ceti's files on projective space: `Basic.lean`
  ($\rho_{\mathrm{FS}}$ and $\alpha_{\mathrm{FS}}$ on $\mathbb C^{n+1}\setminus0$, their
  relation to $\omega_0$ through the radial projection, and the descended
  form $\omega_{\mathrm{FS}}$, by Tau Ceti's
  `TauCeti.SmoothTwoForm.existsUnique_isSymplectic_mpullback_eq` along the
  Hopf map), `Kahler.lean` (closedness, nondegeneracy, the local potentials
  on the affine charts, compatibility with `ofComplexManifold`, `IsKahler`,
  invariance under $\mathrm U(n+1)$, and with *Complex submanifolds* the
  Kähler structure of every complex submanifold), `Normalization.lean` (the
  affine formula on $\mathbb CP^1$, the comparison with Tau Ceti's
  `OnePoint.fubiniStudyForm` through `OnePoint.diffeomorphProjectivization`,
  the area $\pi$ of every line), `Darboux.lean` (the maps $\psi_j$ onto the
  unit ball with $\psi_j^*\omega_0=\omega_{\mathrm{FS}}$) and
  `Lagrangian.lean` ($\mathbb RP^n$ and the Clifford torus).
- **Builds on:** *Complex submanifolds* (only for its corollary in
  `Kahler.lean`); *Standard model*; Tau Ceti's projective space, descent of
  forms, Dolbeault operators and `OnePoint` files.
- **Milestones:** *Fubini–Study form on complex projective space*, and the
  last sentence of *Complex submanifolds of Kähler manifolds*. The design
  file decides the model of the sphere and of the ball (`StdSpace` or
  `EuclideanSpace ℂ`), and how the area of a line is stated (integration of
  the restricted form over Tau Ceti's oriented $\mathbb CP^1$).

### 28. Space of compatible complex structures (needs `design/compatible-structure-space.md`)

- **Files:** `Geometry/Manifold/Instances/CompatibleComplexStructures.lean`
  ($\mathcal J(V,\omega)$, of dimension $n(n+1)$, embedded as a smooth
  submanifold in $\mathrm{End}(V)$, with Tau Ceti's `compatibleTangentSpace` as tangent
  spaces, charts from Tau Ceti's Cayley chart `compatibleCayleyEquiv`), with
  its algebra in `LinearAlgebra/Symplectic/CompatibleTangent/` and its
  Cayley coordinates in `Topology/ComplexStructure/Compatible/Cayley.lean`;
  `Geometry/Manifold/Instances/SiegelUpperHalfSpace.lean` ($\mathcal S_n$
  as a complex manifold); and in `Geometry/Symplectic/CompatibleSpace/`:
  `ComplexStructure.lean` (the structure $\hat J\mapsto-J\hat J$, constant in
  the global Cayley chart, hence integrable), `Kahler.lean` (the
  form $\Omega$ and the trace metric, their invariance under linear
  symplectomorphisms, and `IsKahler`), `LeviCivita.lean`, `Curvature.lean`
  (the curvature and the sign of the sectional curvature),
  `Geodesic.lean` (the geodesics $J\exp(-J\hat Jt)$ and completeness) and
  `Siegel.lean` (for $V$ = `StdSpace ι` the holomorphic diffeomorphism with
  *Siegel upper half space*'s $\mathcal S_n$ and the pulled-back metric).
- **Builds on:** *Nijenhuis tensor* (only `Integrable.lean`); *Almost
  complex manifolds* (only `Metric.lean`); the merged
  *Siegel upper half space* and *Compatible complex structures*; Tau Ceti's
  Cayley files and curvature of connections.
- **The metric:** unlike the convention *The metric* above, the trace metric
  of $\mathcal J(V,\omega)$ is a global `RiemannianBundle` instance on its
  tangent bundle, as Tau Ceti does for its model geometries: it is the
  canonical metric of the space, and Tau Ceti's geodesic API reads the
  Levi-Civita connection from that instance.
- **Milestones:** *Kähler structure on the space of compatible linear complex
  structures*, with integrability from the global Cayley chart, the bounded
  model of $\mathcal S_n$, rather than from the parallel-$J$ criterion, as
  the page advises. The
  design file fixes the curvature convention, which the page gives, and
  whether the manifold is a subtype of `V →L[ℝ] V` or Tau Ceti's type of
  compatible structures.

### 29. Hodge theory (needs `design/hodge-theory.md`)

- **Files:** `Geometry/Manifold/DeRham/Hodge/` (the analytic half of the
  Hodge theorem on a closed oriented Riemannian manifold: every de Rham
  class has a harmonic representative, completing Tau Ceti's
  `Geometry/Manifold/DeRham/Harmonic.lean`, from Tau Ceti's scalar interior
  elliptic regularity `Analysis/Pseudodifferential/DistributionalRegularity.lean`,
  its Rellich theorem and its Fredholm alternative for Gårding forms), and
  `Geometry/Manifold/DeRham/Kahler/` (complex harmonic forms, the Kähler
  identities, the decomposition of $H^k(M;\mathbb C)$ by type, with Tau
  Ceti's `complexDeRhamCohomology` and `SmoothForm.IsOfType`, the
  symmetries of the Hodge numbers, and the evenness of odd Betti numbers),
  with the files outside these folders that the design file lists.
- **Builds on:** *Nijenhuis tensor* (only `Integrable.lean`); *Almost complex
  manifolds* (only `Metric.lean`, for the metric $g_J$ in the milestone);
  Tau Ceti's harmonic forms, Hodge star, types of forms and elliptic
  regularity. The Kähler identities are proved in osculating holomorphic
  charts, not through $\nabla J=0$, so the part does not use *Almost Kähler
  geometry*.
- **Milestones:** *Hodge decomposition on closed Kähler manifolds*, for a
  closed Kähler manifold in the page's sense (`IsKahler` and
  `IsIntegrable`, on a boundaryless manifold), with Betti numbers the
  dimensions of de Rham cohomology. This is the largest part of the page;
  the design file splits it, and proves the analytic half on the whole
  manifold, with regularity and compactness in charts, not through a
  parametrix.

### 30. Energy of pseudoholomorphic curves (needs `design/pseudoholomorphic-energy.md`)

- **Files:** in `Geometry/Symplectic/JHolomorphic/Energy/` (beside Tau Ceti's
  folder of the same name): `Density.lean` (the norm of a linear map from a
  tangent plane of $\Sigma$, measured by $\mathrm{dvol}_\Sigma(\cdot,j\cdot)$,
  to a tangent space, its value on a frame $(e,je)$, and the pointwise
  identity, read on each tangent plane from their vector-space versions,
  with $\bar\partial_J$ Tau Ceti's
  `TauCeti.complexAntilinearPart`), `Metric.lean` (that norm read in
  $g_J$), `Surface.lean` (the energy as an integral over
  the closed surface, Tau Ceti's `integralTopForm`, the integrated
  identity, independence of the area form, the $J$-holomorphic case and
  positivity)
  and `Homology.lean` (for closed $\omega$, $\int_\Sigma u^*\omega$ as the
  pairing of $[\omega]$ with $u_*[\Sigma]$, and the milestone), with the
  comparison of `integralTopForm` with fundamental classes of closed
  oriented surfaces, which Tau Ceti does not have, in files outside
  the folder that the design file lists.
- **Builds on:** *Almost complex manifolds* (only `Metric.lean`); Tau Ceti's
  `IsPseudoholomorphic`, energy densities, integration of top forms and
  smooth singular chains.
- **Milestones:** *Energy identity for J-holomorphic curves*.

### 31. First Chern class of nondegenerate forms

- **Files:** `Geometry/Symplectic/Manifold/FirstChernClass.lean`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.firstChernClass`, *First Chern
  number*'s `firstChernClass` of the complex tangent bundle of a compatible
  $J$, chosen by Tau Ceti's `IsNondegenerate.exists_compatible`; it equals
  the class of every compatible and every taming $J$, since two structures
  taming one form give isomorphic complex bundles, by the merged
  classification of *Symplectic vector bundles*; and it is constant along a
  smooth family $\omega_t$ over $[0,1]$, the slices of a two-form on
  $\mathbb R\times M$, by pulling the tangent bundle back to
  $\mathbb R\times M$ with a structure compatible with the slices, whose
  classes at the two ends agree since the two inclusions are homotopic),
  and `Geometry/Manifold/VectorBundle/Symplectic/FirstChernClass.lean` (the
  classes of pull-backs and transports of complex structures on a vector
  bundle, and of two structures tamed by one form).
- **Builds on:** *First Chern number* (only
  `Topology/VectorBundle/Complex/FirstChernClass.lean`, #784); the merged
  `Symplectic/Classification.lean`, `Symplectic/ComplexStructure/Basic.lean`
  and `Symplectic/Pullback.lean`, and
  `Geometry/Manifold/VectorBundle/Pullback.lean`,
  of *Symplectic vector bundles*; the merged
  `Geometry/Manifold/DifferentialForm/Pullback/Family.lean` of *Moser
  isotopy*.
- **Milestones:** *First Chern class of a nondegenerate two-form*, on a
  Hausdorff σ-compact manifold (for the existence of a compatible $J$). The
  integral class is *First Chern number*'s, the Euler class of the
  determinant line, as `design/first-chern-number.md` plans it for this
  page. No design file is needed.

### 32. Adjunction (needs `design/adjunction.md`)

- **Files:** `Geometry/Manifold/SmoothEmbedding/NormalSpace/ComplexStructure.lean`
  (since $T\Sigma$ is $J$-invariant, $J$ descends to the fibres of Tau
  Ceti's intrinsic normal bundle `TauCeti.SmoothEmbedding.NormalSpace` and
  makes it a smooth complex bundle, with no metric), and in
  `Geometry/Symplectic/Manifold/AlmostComplex/`: `NormalSplitting.lean`
  (the splitting of $TX|_\Sigma$ as a direct sum of symplectic bundles, over
  the surface, through a compatible form on the pulled-back tangent bundle
  and its symplectic complement of $T\Sigma$), `SelfIntersection.lean` (the
  self-intersection number as the Euler number of the normal bundle, with
  the orientation of its complex structure) and `AdjunctionFormula.lean`
  (the formula, with Tau Ceti's `TauCeti.surfaceGenus`).
  `design/adjunction.md` gives the details.
- **Builds on:** *First Chern number* (`FirstChernClass.lean` and
  `ChernNumber/Basic.lean`, #784, and `ChernNumber/Axioms.lean` for
  additivity and $c_1(T\Sigma)$, #788); *Symplectic vector bundles*
  (complex structures, direct sums and pull-backs, merged); Tau Ceti's
  normal bundles of smooth embeddings
  (`Geometry/Manifold/SmoothEmbedding/NormalSpace/`).
- **Milestones:** *Adjunction formula*, with the self-intersection number
  defined as the page defines it, so that no Poincaré duality is needed;
  the equality with $Q_X([\Sigma],[\Sigma])$ for closed $X$ is not part of
  the milestone. The example of plane curves is proved by *Projective
  hypersurfaces*.

### 33. Chern classes (needs `design/chern-classes.md`)

- **Files:** in `Topology/VectorBundle/Complex/ChernClass/`: the Chern
  classes $c_k$ and the total class of a complex vector bundle in integral
  singular cohomology, by the projective bundle and Tau Ceti's Leray–Hirsch
  files (`AlgebraicTopology/Cohomology/LerayHirsch/`), with $c_1$ equal to
  *First Chern number*'s `firstChernClass`; naturality, the Whitney sum
  formula, the top class as Tau Ceti's `TauCeti.complexEulerClass`; the
  cohomology ring of $\mathbb CP^n$, which Tau Ceti has only additively.
  The evaluation of the Euler class of the tangent bundle of a closed
  oriented manifold on its fundamental class as its Euler characteristic,
  and the general infrastructure (the ring of even integral classes,
  Leray–Hirsch for bundles, projective bundles), are in files outside that
  folder, which `design/chern-classes.md` lists.
- **Builds on:** *First Chern number* (`FirstChernClass.lean`, #784, only
  for the comparison of $c_1$); Tau Ceti's Euler and Thom classes, cup
  products, Leray–Hirsch files and Poincaré–Hopf theorem for gradients of
  Morse functions. No Poincaré duality is needed.
- **Milestones:** none by itself; it provides what *Projective
  hypersurfaces* needs. `design/chern-classes.md` gives the construction
  (the projective bundle, with Hatcher's proof of the Whitney formula and a
  one-step splitting principle), the proof of the Euler characteristic
  formula (Poincaré–Hopf for the gradient of a Morse function) and the
  issues.

### 34. Projective hypersurfaces (needs `design/projective-hypersurfaces.md`)

- **Files:** in `Geometry/Manifold/Projectivization/Hypersurface/` (beside
  Tau Ceti's `Geometry/Manifold/Projectivization/ZeroLocus.lean`, whose
  `isManifold_complexProjectiveZeroLocus` makes a smooth hypersurface a
  complex submanifold): the tangent bundle of $\mathbb CP^{n+1}$ plus a
  trivial line as $H^{\oplus(n+2)}$, with $H$ Tau Ceti's
  `Projectivization.twistCore 1`; the normal bundle of a hypersurface of
  degree $d$, Tau Ceti's `TauCeti.SmoothEmbedding.NormalSpace` bundle over
  `ℂ`, as the restriction of $H^{\otimes d}$, through the derivative
  of the polynomial; $\langle\iota^*h^n,[M]\rangle=d$; then the total Chern class
  and $c_1$ of $M$; the Euler characteristic; the numbers for surfaces in
  $\mathbb CP^3$ and threefolds in $\mathbb CP^4$, with Tau Ceti's Lefschetz
  theorems for the Betti numbers; and the genus of a smooth plane curve,
  from its Euler characteristic $d(3-d)$. The bundles on projective space,
  a splitting along an embedding and the Euler characteristic of a compact
  complex manifold are in files outside that folder, which
  `design/projective-hypersurfaces.md` lists.
- **Builds on:** *Chern classes*; *First Chern number* (only Poincaré
  duality, #810); Tau Ceti's projective space, line bundles, zero loci,
  Veronese maps and Lefschetz theorems, and its normal bundles and tubular
  neighbourhoods of smooth embeddings
  (`Geometry/Manifold/SmoothEmbedding/NormalSpace/`,
  `Geometry/Manifold/TubularNeighborhood/`).
- **Milestones:** *Chern classes of projective hypersurfaces*, and the
  example of *Adjunction formula*. Tau Ceti's Lefschetz theorems assume a
  neighbourhood of the hyperplane section that retracts onto it; the design
  file supplies it for smooth sections, or finds another route to the
  connectedness and simple connectivity it needs. The signature and $b^\pm$
  are stated with the signature theorem as a hypothesis (see *Departures*).

### 35. Lie group actions

Shared with `atlas/symplectic-fibrations.md`, whose parts extend it.

- **Files:** `Geometry/Manifold/GroupAction/Circle.lean` (circle actions
  in period one: the generator $\xi_1$, the flow of $X_{\xi_1}$ as the
  action of $t\mapsto$ `Circle.exp (2 * π * t)`, of period one, and the
  fixed points of a circle action as the zeros of $X_{\xi_1}$, from Tau
  Ceti's `TauCeti.globalFlow_fundamentalVectorField`), and
  `Geometry/Manifold/GroupAction/InvariantPrimitive.lean` (for a compact
  group, an invariant exact form has an invariant primitive, by averaging
  a primitive with Tau Ceti's
  `TauCeti.SmoothForm.measureAverage`, `mpullback_smul_measureAverage` and
  `mextDerivₗ_measureAverage`).
- **Builds on:** Mathlib, Tau Ceti (fundamental vector fields and their
  flows, averaging of forms).
- **Milestones:** none; it serves *Hamiltonian circle actions*, *Minimal
  coupling* and *Equivariant localization*, and the fibrations page.
- The actions themselves, their fundamental vector fields, orbits, fixed
  sets, Bochner linearization and the quotient manifold theorem are Tau
  Ceti's (`Geometry/Manifold/GroupAction/`), so the part is small. No design
  file is needed.

### 36. Moment maps

Shared with `atlas/symplectic-fibrations.md`, whose parts extend it.

- **Files:**
  `Geometry/Symplectic/Hamiltonian/MomentMap/WeaklyHamiltonian.lean` (if
  every $X_\xi$ of a symplectic action is Hamiltonian, the Hamiltonians can
  be chosen linear in $\xi$, so that a moment map exists, by choosing them
  on a basis; two such choices differ by a linear map to the locally
  constant functions) and
  `Geometry/Symplectic/Hamiltonian/MomentMap/Obstruction.lean` (on a
  connected $M$: the class of `momentCocycle` of $-\mu$ in Tau Ceti's
  `TauCeti.LieModule.Cohomology.cohomology ℝ 𝔤 (TrivialLieModule ℝ 𝔤 ℝ) 2`,
  reached through `(twoCochainEquiv ℝ 𝔤 _).symm` and `moduleCatKerHomologyClass`,
  a cycle by `momentCocycle_mem_twoCocycle` and `d₂₃_twoCochainEquiv`; its
  independence of $\mu$; and that it vanishes, by
  `moduleCatHomologyClass_eq_zero_iff` and `twoCochainEquiv_d_one`, exactly
  when $\mu$ can be shifted by a constant to one whose cocycle is zero,
  which for connected $G$ is equivariant).
  No second cohomology of its own is defined.
- **Builds on:** Mathlib (`LieModule.Cohomology.twoCocycle`, `d₁₂`, `d₂₃`),
  Tau Ceti (`TauCeti/Algebra/Lie/Cohomology/ChevalleyEilenberg.lean`:
  `TauCeti.LieModule.Cohomology.cohomology`, `twoCochainEquiv`,
  `twoCochainEquiv_d_one`, `d₂₃_twoCochainEquiv`;
  `TauCeti/Algebra/Homology/ModuleCat/Basic.lean`:
  `HomologicalComplex.moduleCatKerHomologyClass`,
  `HomologicalComplex.moduleCatHomologyClass_eq_zero_iff`;
  `TauCeti.SmoothTwoForm.momentCocycle` with
  `IsMomentMap.momentCocycle_eq`, `momentCocycle_mem_twoCocycle`,
  `momentCocycle_add_const`, `momentCocycle_apply_eq_poissonBracket`,
  `IsEquivariantMomentMap.momentCocycle_eq_zero`,
  `IsMomentMap.isEquivariantMomentMap_of_momentCocycle_eq_zero`,
  `IsMomentMap.isEquivariantMomentMap_iff_momentCocycle_eq_zero_and_apply_smul`;
  `TauCeti.SmoothTwoForm.interiorClass_eq_zero_iff`).
- **Milestones:** *Equivariance and the obstruction to an equivariant moment
  map*, as one theorem in the page's sign. No design file is needed.

### 37. Equivariant normal forms

- **Files:** `Geometry/Symplectic/Manifold/EquivariantDarboux.lean` (named
  like Tau Ceti's file: the page's form of Tau Ceti's chart, an equivariant
  symplectomorphism from an invariant open neighbourhood of $0$ in
  $(T_pM,\omega_p)$ onto one of $p$, sending $0$ to $p$) and
  `Geometry/Symplectic/Hamiltonian/WeightModel/NormalForm.lean` (named like
  Tau Ceti's file: for a torus with a moment map, Tau Ceti's weight chart
  read on `StdSpace (Fin n)` with `stdForm`, through *Standard model*'s
  comparison with the product model, with the period-one weights
  $\alpha^{\mathrm{TC}}/2\pi$, which lie in the character lattice, and the
  quadratic formula for $\mu=-\mu^{\mathrm{TC}}$).
- **Builds on:** *Standard model* (merged); Tau Ceti
  (`TauCeti.SmoothTwoForm.IsSymplectic.exists_equivariant_darbouxChart`,
  `TauCeti.SmoothTwoForm.IsMomentMap.exists_weightModelChart`).
- **Milestones:** *Equivariant Darboux theorem and quadratic local moment
  maps*, at a point fixed by $G$ (see `ERRATA.md`). No design file is
  needed: both halves are translations of Tau Ceti's theorems, which already allow zero weights and need neither
  compactness of $M$ nor an isolated fixed point.

### 38. Hamiltonian circle actions (needs `design/hamiltonian-circle-actions.md`)

- **Files:** `Geometry/Manifold/DeRham/PoincarePairing/Nondegenerate.lean`
  (in Tau Ceti's folder `PoincarePairing/`: on a closed oriented
  $m$-manifold, a closed $(m-1)$-form whose wedge with every closed
  one-form has integral zero is exact), and
  `Geometry/Symplectic/Hamiltonian/CircleAction.lean` (a Hamiltonian circle
  action on a closed manifold has a fixed point, at an extremum of $H$; if
  the action has a fixed point, then $\int_M\gamma(X)\,\omega^n=0$ for every
  closed one-form $\gamma$, since $\gamma$ is cohomologous to its average
  over the circle, which pairs $X$ to a constant, zero at the fixed point;
  with the cup-product hypothesis, the action is Hamiltonian).
- **Builds on:** *Lie group actions* (only `Circle.lean`); *Moment maps*
  (only `MomentMap/WeaklyHamiltonian.lean`); Tau Ceti
  (`TauCeti.deRhamCohomology` with
  `wedge`, `TauCeti.poincarePairing`, `interiorClass_eq_zero_iff`,
  `integralTopForm_mextDeriv_eq_zero`, periods of closed one-forms,
  averaging of forms); the merged Hodge theorem of *Hodge theory*
  (`Geometry/Manifold/DeRham/Hodge/Basic.lean`).
- **Milestones:** *Frankel–Ono Hamiltonianity criterion*.
- **The design file decides:** the route to the nondegeneracy of the
  pairing in degrees $(1,m-1)$: through the library's singular duality
  (`AlgebraicTopology/Cohomology/CompactSupport/Duality/Manifold.lean`)
  and Tau Ceti's comparison of de Rham and singular cohomology
  (`Geometry/Manifold/SmoothSingular/DeRham.lean`), or directly from
  periods of closed one-forms; and how the hypothesis on
  $[\omega]^{n-1}\smile-$ is stated with Tau Ceti's de Rham classes. The
  page's route through the Poincaré dual of an orbit is replaced by the
  integral identity above, which needs no homology class of an orbit.

### 39. Minimal coupling (needs `design/minimal-coupling.md`)

- **Files:** in `Geometry/Symplectic/Coupling/`: `Basic.lean` (given a
  circle bundle $P\to B$, principal, and a family $\tau_\lambda$ on $B$, the
  coupling forms on $P\times[a,b]$: closed, invariant, with
  $\iota_X\omega=-d\lambda$ and reduced forms $\tau_\lambda$; they are
  nondegenerate when the $\tau_\lambda$ are, and their existence forces the
  cohomological condition), `Existence.lean` (their existence under that
  condition), `Uniqueness.lean` (two such forms for the same
  $P$ and $\tau_\lambda$ are related by an equivariant symplectomorphism
  preserving $\lambda$, by an equivariant Moser isotopy tangent to the
  levels) and `Converse.lean` (a compact band
  $H^{-1}([a,b])$ of a symplectic manifold with a Hamiltonian circle
  action, free on the band, with $H$ of image $[a,b]$ there, is of this
  form; the band is a manifold with boundary $H^{-1}(a)\cup H^{-1}(b)$);
  `Geometry/Symplectic/Moser/Equivariant.lean` (a Moser isotopy built from
  invariant primitives of a family of invariant forms is equivariant);
  `Geometry/Manifold/FiberBundle/Principal/RealChernClass.lean` (the real
  first Chern class $-(2\pi)^{-1}[F_\alpha]$ of a circle bundle); and
  `Geometry/Manifold/GroupAction/PrincipalBundle.lean` (a free action of a
  compact Lie group makes a principal bundle over the quotient manifold).
- **Builds on:** *Lie group actions* (only `Circle.lean`); the merged circle
  connection forms of *First Chern number*
  (`Geometry/Manifold/FiberBundle/Principal/CircleConnection.lean`,
  `SymplecticGeometry.IsCircleConnectionForm` with its curvature, which is
  normalized on `circleLieGenerator`, so that the page's connection form is
  $(2\pi)^{-1}$ times it); *Smooth families* (merged: families of
  primitives); Tau Ceti (principal bundles, the quotient manifold theorem,
  Moser's theorem with given primitives).
- **Milestones:** *Minimal coupling*, with the bundle $P$ fixed in the
  uniqueness statement and the boundary of the converse, as the page
  corrects the book.
- **The design file decides:** the representation of $P\times[a,b]$, a
  manifold with boundary through `unitInterval` or `Set.Icc a b`, and of
  the compact manifold with boundary in the converse; the flows on it (each
  Moser field keeps $H$ constant, so its flow maps the boundary to itself);
  and how the Chern class convention of *First Chern number* matches the
  page's cohomological condition.

### 40. Coisotropic reduction (needs `design/coisotropic-reduction.md`)

- **Files:** `Geometry/Manifold/Foliation/Transport.lean`,
  `Foliation/LeafSpace/Basic.lean` and `Foliation/LeafSpace/Smooth.lean`
  (in Tau Ceti's folder of foliations: the page's regularity condition on a
  foliation, through slices meeting every leaf at most once, and the unique
  smooth structure on the leaf space for which the projection
  is a submersion whose vertical spaces are the leaf directions), and in
  `Geometry/Symplectic/Coisotropic/`: `Reduction.lean` (regular coisotropic
  reduction: the leaf space of Tau Ceti's characteristic foliation, of
  dimension $2n-2k$, with the unique symplectic form pulling back to
  $i^*\omega$, from `TauCeti.SmoothTwoForm.existsUnique_isSymplectic_mpullback_eq`)
  and `Lagrangian/Basic.lean`, `Lagrangian/Immersion.lean` and
  `Lagrangian/Injective.lean` (clean intersections of a Lagrangian
  embedding with a coisotropic immersion, the characteristic directions of the intersection,
  their local leaf spaces, the Lagrangian immersion from a countable
  disjoint union of them, the transverse case, and injectivity when the leaf
  space of $Q$ is Hausdorff and every leaf meets $L$ in a connected set).
- **Builds on:** Tau Ceti (`TauCeti.SmoothForm.characteristicFoliation`,
  `TauCeti.Foliation.leaf`, `TauCeti.IsInvolutiveDistribution.exists_flatChart`,
  coisotropic and Lagrangian maps, `IsLagrangianMap.isLagrangianImmersion_of_comp_submersion`,
  `TauCeti.SymplecticForm.IsLagrangian.reduction_map`); the merged
  *Symplectic neighbourhoods* (characteristic foliations of coisotropic
  embeddings).
- **Milestones:** *Regular coisotropic reduction*, *Clean reduction of
  Lagrangian submanifolds*.
- **The design file decides:** how $Q$ is given (a coisotropic immersion, of
  which Tau Ceti's `IsCoisotropicEmbedding` is a case), the type of the
  leaf space and how its charts come from the slices, and the form of "clean intersection" for
  maps.

### 41. Hamiltonian reduction (needs `design/hamiltonian-reduction.md`)

- **Files:** in `Geometry/Symplectic/Hamiltonian/Reduction/`, beside Tau
  Ceti's files: `ZeroLevel/` (Marsden–Weinstein reduction at the zero
  level for a connected group acting freely and properly on the level
  only: the quotient manifold theorem applied to the level's own action,
  the unique reduced form, the dimension, that the level is coisotropic
  with the orbits as characteristic leaves, and
  $T_{[p]}(M/\!/G)\cong\ker d\mu(p)/\operatorname{im}L_p$ with the induced
  form) and `CoadjointOrbit/` (reduction at an embedded coadjoint
  orbit: transversality, the reduced form with
  $\pi^*\omega_{\mathrm{red}}=i^*\omega+(\mu|_Q)^*\omega_{\mathcal O}$, and
  the symplectomorphism with the reduced space at zero of
  $M\times\mathcal O$, whose moment map is $\mu(p)-\eta$).
- **Builds on:** Tau Ceti (the quotient
  manifold theorem, the regular-level atlas `IsMomentMap.levelChartedSpace`,
  the reduced form of level data
  `IsEquivariantMomentMap.existsUnique_isSymplectic_mpullback_eq_mpullback`,
  the product moment map `IsEquivariantMomentMap.prod`, the coadjoint orbit
  `Module.Dual.coadjointOrbitForm`).
- **Milestones:** *Marsden–Weinstein reduction*, *Reduction at a coadjoint
  orbit and the shifting construction*.
- **The design file decides:** how the reduction is stated when properness
  holds only on the level (Tau Ceti asks for a proper action on $M$), how
  an embedded coadjoint orbit is given (the orbit map
  $G/G_\eta\to\mathfrak g^*$ as an embedding), and the comparison of
  the quotient by $G$ with Tau Ceti's quotient by $G_c$.

### 42. Convexity (needs `design/convexity.md`)

- **Files:** `Geometry/Symplectic/Manifold/FixedComponent.lean` (the fixed
  components as symplectic submanifolds),
  `Geometry/Symplectic/Hamiltonian/MomentMap/LocalConvexity.lean` (local
  convexity of a torus moment map at every point, from the weight chart of
  the stabilizer), and
  `Geometry/Symplectic/Hamiltonian/MomentMap/Convexity.lean` (convexity of
  the image and connectedness of every fibre, and with Tau Ceti's
  `range_subset_convexHull_image_fixedPoints` the image as the convex hull
  of the values on the fixed components).
- **Builds on:** Tau Ceti (the local-to-global theorem of
  `Analysis/Convex/LocalToGlobal.lean`, `MomentMap/ConvexHull.lean`,
  `FixedPoints.lean`,
  `TauCeti.finite_connectedComponents_fixedPoints_of_compactSpace`,
  `IsNondegenerate.exists_isSymplecticSubmanifoldEmbedding_fixedPointsOfFinrank`,
  the weight chart `IsMomentMap.exists_weightModelChart` and the local
  convexity of the weight model in `WeightModel/Convexity.lean`).
- **Milestones:** *Convexity and connectedness of moment-map fibers*,
  including the fibres over critical values.
- **The design file decides:** the route to connectedness of every fibre,
  which the page leaves open between the limiting argument of the book and
  Bjorndahl–Karshon's local-to-global theorem with the local normal form
  along orbits (Tau Ceti has its linear part, `MomentMap/LinearNormalForm.lean`);
  and whether it needs an induction on the torus.

### 43. Equivariant localization (needs `design/equivariant-localization.md`)

- **Files:** in `Geometry/Manifold/DifferentialForm/Equivariant/`:
  `Basic.lean` (the Cartan differential $d-\hbar\,\iota_X$ of a smooth
  vector field on forms of mixed degree, and its square, which vanishes on
  invariant forms) and `Localization.lean` (the localization
  lemma: the integral of an equivariantly closed form does not change
  when it is multiplied by $F(d_\hbar\theta)$, for an invariant one-form
  $\theta$ and $F(0)=1$, which concentrates it near the fixed points); and
  `Geometry/Symplectic/Hamiltonian/Localization/` (the
  Duistermaat–Heckman formula for $e^{\omega-\hbar H}$ at isolated fixed
  points, with the actual period-one tangent weights, and its value at
  $\hbar=0$ as the symplectic volume).
- **Builds on:** *Lie group actions* (`Circle.lean`); *Equivariant normal
  forms* (the period-one weights at a fixed point); Tau Ceti (the Cartan
  identity `TauCeti.mlieDerivForm_eq_interior_mextDeriv_add`, Stokes'
  theorem `TauCeti.integralTopForm_mextDeriv_eq_zero`, invariant metrics
  `TauCeti.exists_contMDiffRiemannianMetric_inner_mfderiv`).
- **Milestones:** *Duistermaat–Heckman localization*.
- **The design file decides:** how forms with a complex parameter $\hbar$
  are represented (Tau Ceti integrates real top forms), and how the local
  contribution at a fixed point is computed in the weight chart.

### 44. Kähler stability (needs `design/kahler-stability.md`)

- **Files:** `Geometry/Lie/Complexification.lean`
  (the complexification $G^{\mathbb C}$ of a compact connected Lie group,
  given as data with the decomposition
  $G^{\mathbb C}=\exp(i\mathfrak g)G$), and in
  `Geometry/Symplectic/Hamiltonian/MomentMap/`: `KempfNess/` (the
  holomorphic action extending that of $G$, the Kempf–Ness function $\Phi_p$,
  its existence and uniqueness, descent to $G^{\mathbb C}/G$, convexity
  along geodesics, its critical points, the gradient flow of
  $\tfrac12\|\mu\|^2$ and its convergence, through a Łojasiewicz inequality,
  and the three stability conditions with their characterizations)
  and `HilbertMumford.lean` (the weights $w_\mu(p,\xi)$ for $\xi\in\Lambda$,
  the limits $p^+_\xi$, the moment-weight inequality and the numerical
  criteria); the Łojasiewicz inequality's files are those of
  `design/kahler-stability.md`.
- **Builds on:** Tau Ceti (`TauCeti.SmoothTwoForm.IsKahler`, invariant inner
  products
  `TauCeti.Lie.exists_isSymm_posDef_continuousBilinearMap_adjoint_invariant`,
  limits of gradient trajectories `tendsto_maximalIntegralCurve_neg_mgradient_of_mapClusterPt`).
- **Milestones:** *Kempf–Ness correspondence*, *Hilbert–Mumford numerical
  criteria*.
- **The design file decides:** how $G^{\mathbb C}$ and its action are
  given (as data with hypotheses, or constructed); where the analytic
  Łojasiewicz inequality comes from, which the convergence of the gradient
  flow needs and which neither library has; and the split of the part into
  issues, the Kempf–Ness milestone first.

### 45. Cauchy–Riemann operators on the sphere (needs `design/cauchy-riemann-sphere.md`)

Differential topology and complex analysis only; it waits for no part of
`atlas/symplectic-fibrations.md`.

- **Files:** in `Geometry/Manifold/Instances/OnePoint/CauchyRiemann/`:
  `Basic.lean` (for $J\in\mathcal J$, the operator $D_J$ on sections of the
  degree-one line bundle $L=\mathcal O(1)$, Tau Ceti's `OnePoint.twistCore`,
  taken as Tau Ceti's real Cauchy–Riemann operator for $J$: the
  $(0,1)$-part `TauCeti.SmoothAlmostComplexStructure.zeroOnePart` of a fixed
  connection on $L$, a `TauCeti.IsRealCauchyRiemannOperator` by
  `IsCovariantDerivativeOn.isRealCauchyRiemannOperator_zeroOnePart`; the
  connection is chosen so that $D_i$ is the $\bar\partial$-operator of $L$;
  the identification of $\Lambda^{0,1}_J$ with $\Lambda^{0,1}_i$ by
  projection, an isomorphism
  because $J\ne-i$ at every point), `Sobolev.lean` (only what Tau Ceti's
  `Geometry/Manifold/VectorBundle/Sobolev/` lacks: its
  `TauCeti.IsRealCauchyRiemannOperator.sobolevL` realizes only operators of
  the fixed complex structure; this file realizes $D_J$ for every $J$, by
  the projection of `Basic.lean`, as a bounded map from
  `TauCeti.SobolevSection` ($W^{k+1,2}$) to `TauCeti.zeroOneSobolevSections`
  ($W^{k,2}$) for every $k$, shows that it depends
  continuously on $J$ in the operator norm, and gives the elliptic
  regularity of its kernel), `Standard.lean` ($D_i$ is
  surjective with kernel $H^0(\mathcal O(1))$ of dimension two, from Tau
  Ceti's `OnePoint.finrank_holomorphicTwistSections` and the solution of
  $\bar\partial$ on $(0,1)$-forms,
  `TauCeti.SmoothForm.IsOfType.exists_delBar_eq_projectivization`, extended
  to $\mathcal O(1)$ by the splitting into two charts that the page
  describes) and `Kernel.lean` (real index four for all $J$, by Tau Ceti's
  `Continuous.index_eq_of_preconnectedSpace` on the connected $\mathcal
  J$; every nonzero element of $E_J=\ker D_J$ has exactly one zero, which
  is simple, from integrability, read in isothermal charts of $J$, and the
  local solution of $\bar\partial$; hence
  $\dim E_J=2$ and $D_J$ onto; the spaces $E_J$ form a continuous rank-two
  family in $C^\infty(L)$, from the inverse of $D_J$ stabilized by a
  projection onto $E_{J_0}$).
- **Builds on:** the merged *Isothermal coordinates* (integrability of $J$,
  `TauCeti.SmoothAlmostComplexStructure.isIntegrable_of_finrank_eq_two`) and
  *Symplectic vector bundles* (contractibility of the tamed structures,
  which makes $\mathcal J$ connected); Tau Ceti (line bundles on
  `OnePoint ℂ`, real Cauchy–Riemann operators and Sobolev sections in
  `Geometry/Manifold/VectorBundle/`, Fredholm families in
  `Analysis/Fredholm/`).
- **Milestones:** none; it serves *Diffeomorphisms of the 2-sphere*.
- **The design file decides:** how $D_J$ for a varying $J$ meets Tau
  Ceti's realization, which is for one complex structure (by the projection
  of `Basic.lean`, or by `sobolevL` for the complex atlas that $J$
  defines, with a comparison of the spaces); whether higher Sobolev orders
  are needed or $W^{1,p}$ with Tau Ceti's Rellich and Morrey results
  suffices; the form of elliptic regularity it needs; and the zero count,
  which the page reduces to integrability, local
  solvability of $\bar\partial$ on a disc and the sum of indices of the
  zeros of a section, given by Tau Ceti's
  `TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_analyticOrderNatAt`.

### 46. Diffeomorphisms of the 2-sphere (needs `design/sphere-diffeomorphisms.md`)

- **Files:** in `Geometry/Diffeomorphism/Sphere/`, beside Tau Ceti's
  files of that folder: `ComplexStructure.lean` (the space $\mathcal J$
  with its topology, the pull-back $\phi^*J$, its continuity in $\phi$,
  and the contraction of $\mathcal J$ onto $i$), `Uniformization.lean`
  (the map $\sigma(J)$ built from sections of $E_J$ vanishing at $0$ and
  $\infty$, its continuity, and that it is the unique biholomorphism
  $(S^2,J)\to(S^2,i)$ fixing $0,1,\infty$, from the zero count of $E_J$
  and Tau Ceti's
  `Diffeomorph.eq_refl_of_apply_zero_one_infty_eq_self`), `Mobius.lean`
  ($\mathrm{PSL}(2,\mathbb C)$ as the stabilizer of $i$ in $\mathrm{Diff}^+$,
  from `Diffeomorph.exists_coe_eq_smul`, with its subspace topology equal
  to its Lie group topology, and its deformation retraction onto
  $\mathrm{SO}(3)$ by the polar decomposition), `Trivialization.lean` (the
  homeomorphism $\mathrm{Diff}^+(S^2)\cong\mathcal J\times\mathrm{PSL}(2,\mathbb
  C)$ over $\mathcal J$) and `Smale.lean` (sharing its name with Tau
  Ceti's `Geometry/Diffeomorphism/Smale.lean`, on the conjecture for $S^3$:
  the strong deformation retraction of $\mathrm{Diff}^+(S^2)$ onto
  $\mathrm{SO}(3)$, with $\pi_0=0$ and $\pi_1\cong\mathbb Z/2$ from Tau
  Ceti's `TauCeti.specialOrthogonalGroupFundamentalGroupMulEquiv`).
- **Builds on:** *Cauchy–Riemann operators on the sphere*; the merged
  *Symplectic vector bundles*; Tau Ceti (`TauCeti.Diff`, the weak Whitney
  topology, `TauCeti.orthogonalToDiffSphere`, Möbius transformations of
  `OnePoint ℂ`).
- **Milestones:** *Diffeomorphisms of the 2-sphere form a trivial principal
  bundle over the complex structures*, *Smale's theorem on the
  diffeomorphism group of the 2-sphere*, both by the proof that the page
  proposes, which reads $\mathrm{Diff}^+(S^2)$ as a product over
  $\mathcal J$.
- **The design file decides:** the orientation-preserving subgroup
  $\mathrm{Diff}^+(S^2)$ (through Tau Ceti's orientations or the degree,
  `Geometry/Diffeomorphism/Degree.lean`), the comparison of `OnePoint ℂ`
  with the unit sphere, and the form of "strong deformation retract".

### 47. Parallel transport (needs `design/parallel-transport.md`)

- **Files:** in Tau Ceti's folder `Geometry/Manifold/Submersion/`:
  `HorizontalLiftField.lean` (horizontal lifts of vector fields),
  `ParallelTransport/Basic.lean` and `ParallelTransport/Smooth.lean` (for
  an Ehresmann connection
  `TauCeti.IsEhresmannConnection` on a proper submersion, horizontal lifts
  of smooth paths of the base exist and are unique; parallel transport
  `TauCeti.IsEhresmannConnection.parallelTransport` between fibres is a
  diffeomorphism, independent of the parametrization, compatible with
  concatenation and inversion, and smooth in a smooth family of paths),
  `RadialTrivialization.lean` (transport along rays from the centre of
  a chart ball trivializes the submersion over the ball, so a proper
  surjective submersion is locally trivial, the direction of Exercise 6.1.1
  that Tau Ceti lacks) and `Curvature.lean` (the curvature
  $[v_1^\sharp,v_2^\sharp]^{\mathrm{Ver}}=[v_1^\sharp,v_2^\sharp]-[v_1,v_2]^\sharp$,
  tensorial in $v_1,v_2$; it vanishes exactly when the horizontal
  distribution is involutive). A connection given by a two-form
  nondegenerate on the fibres, $\mathrm{Hor}=\mathrm{Ver}^\tau$, is
  *Symplectic fibrations*' and not this part's.
- **Builds on:** Tau Ceti (`TauCeti.IsEhresmannConnection` with
  `horizontalLift`, time-dependent flows and their completeness criteria,
  `Manifold.IsSubmersion`).
- **Milestones:** none; it serves *Symplectic fibrations* and *Coupling
  forms*.
- **The design file decides:** whether the transport is stated for proper
  submersions or for locally trivial maps with compact fibre (the two agree
  by `RadialTrivialization.lean`), how fibres are given as manifolds (Tau
  Ceti's regular-fibre atlas `TauCeti.ManifoldTotalSpace.fiberChartedSpace`
  or reading in charts), and the smoothness in parameters that the
  trivialization needs.

### 48. Symplectic fibrations (needs `design/symplectic-fibrations.md`)

- **Files:** in `Geometry/Manifold/FiberBundle/`: `MapFiber.lean` and
  `StructureGroup.lean` (the atlases of a smooth map `π` with fibre $F$,
  Tau Ceti's `TauCeti.MapFiber.Atlas` with `IsContMDiff`, with structure
  group $H\le\mathrm{Diff}(F)$ and its reductions; oriented and symplectic
  atlases; the bridge from Tau Ceti's `ContMDiffFiberBundle` and
  `AssociatedBundle`); in `Geometry/Symplectic/Fibration/`: `Basic.lean`
  (the predicate that a
  form restricts to the fibre forms, with its independence of the chart;
  compatible symplectic forms, for a symplectic atlas and, with an
  orientation, for an oriented one), `HorizontalDistribution.lean` (a
  two-form that
  restricts to the fibre forms defines the Ehresmann connection
  $\mathrm{Ver}^\tau$; two forms give the same connection exactly when their
  difference vanishes on vertical vectors; every connection arises so;
  connection two-forms, which are
  vertically closed; they exist, by a partition of unity, and form a convex
  set), `Connection.lean` (every connection with symplectic parallel
  transport comes from a connection two-form;
  and the milestone that $\Gamma_\tau$ is symplectic exactly when
  $\tau$ is vertically closed, by the page's route through Cartan's
  formula, Tau Ceti's `TauCeti.mlieDerivForm_eq_interior_mextDeriv_add`),
  `LocalForm.lean` (the normal form
  $\tau=\sigma+\sum_i\alpha_i\wedge dx_i+\sum_{i<j}f_{ij}\,dx_i\wedge dx_j$
  in a symplectic chart over a coordinate patch, and the horizontal lifts
  $(\partial_i,X_i)$ with $\iota(X_i)\sigma=\alpha_i$, reused by *Coupling
  forms*) and `SymplecticFibres.lean` (a closed manifold fibred over $B$
  with a closed two-form symplectic on every fibre is a symplectic
  fibration with these fibre forms, by parallel transport of
  $\mathrm{Ver}^\omega$ along radial lines, the page's second route).
- **Builds on:** *Parallel transport*; Tau Ceti (fibre bundles, Lie
  derivatives and Cartan's formula, smooth partitions of unity of Mathlib).
- **Milestones:** *Fibrations with symplectic fibres are symplectic
  fibrations*, *Symplectic connections correspond to vertically closed
  2-forms*.
- **The design file decides:** the representation of atlases (a set of
  trivializations or an indexed family, how a reduction is compared with
  the given atlas) and how much of the fibre-as-manifold API of Tau Ceti it
  uses.

### 49. Compatible symplectic forms (needs `design/compatible-symplectic-forms.md`)

- **Files:** in `Geometry/Symplectic/Fibration/`: `ClosedExtension.lean` (a
  closed extension $\tau$ of the fibre forms in a class $a$ with
  $\iota_b^*a=[\sigma_b]$, by the page's step 1, through the homotopy
  invariance `TauCeti.deRhamCohomology.map_eq_of_homotopy` on the preimage
  of a contractible open set; and the converse, that a compatible form
  gives $a$), `Thurston.lean` ($\tau+K\pi^*\beta$ symplectic for large
  $K$ on a compact $M$, and the milestone),
  `ChernClass.lean` (the vertical bundle of a symplectic fibration as a
  symplectic vector bundle over $M$, with the merged `Subbundle.lean` and
  `Symplectic/Basic.lean`; its real first Chern class as a de Rham class;
  its restriction to a fibre is $c_1(TF_b)$; the criterion) and
  `Surface.lean` (the surface milestone, with compatibility with the
  orientation). The real first Chern class, built by Chern–Weil for the
  determinant line, natural under pull-back, and compared with the
  library's `SymplecticGeometry.Bundle.firstChernClass` only over closed
  oriented surfaces, through Chern numbers; the formula
  $c_1(TF)=\chi(F)/\mathrm{area}\cdot[\sigma]$; and the family of area
  forms made symplectic by Moser's argument with a parameter in the base
  (`Geometry/Symplectic/Moser/Parameter.lean`) are in files that the
  design file gives.
- **Builds on:** *Symplectic fibrations* (only `Basic.lean` and
  `HorizontalDistribution.lean`), *Minimal coupling* (only
  `RealChernClass.lean`); the merged *Symplectic vector bundles*, *First
  Chern number*, *Moser isotopy* and *Smooth families*
  (`DeRham/SmoothFamily/GoodCover.lean`, which an issue of the design file
  generalizes to a manifold parameter); Tau Ceti (de Rham cohomology and its
  homotopy invariance).
- **Milestones:** *Thurston's theorem on symplectic fibrations*, *Chern
  class criterion for compatible symplectic forms*, *Symplectic forms on
  surface bundles with fibre genus different from one*. The last follows
  the page's elementary route, not the book's reduction of a principal
  bundle with structure group $\mathrm{Diff}^+(F)$.
- **The design file decides:** the de Rham first Chern class over a
  general base (the merged Chern–Weil file treats circle bundles over
  surfaces; the general case needs a connection on the unit circle bundle
  of the determinant line and the comparison with the integral class), and
  how the hypothesis $c_1(TF)=\lambda[\sigma]$ is stated with it.

### 50. Principal connections (needs `design/principal-connections.md`)

- **Files:** in `Geometry/Manifold/FiberBundle/Principal/`, beside the
  merged `CircleConnection.lean` and `BasicForm.lean`: `Connection/`
  (`Basic.lean`, `Existence.lean` and `Curvature.lean`: connection
  one-forms with values in `GroupLieAlgebra I G`,
  `SymplecticGeometry.IsConnectionForm`: $A(p\xi)=\xi$ and
  $A_{pg}(vg)=\mathrm{Ad}(g^{-1})A_p(v)$; their horizontal spaces; existence
  over a paracompact base and the affine structure over
  $\Omega^1(B,\mathrm{ad}P)$; the curvature $F_A=dA+\tfrac12[A\wedge A]$,
  horizontal and equivariant, with $F_A(X,Y)=-A([X,Y])$ on horizontal
  $X,Y$; and the comparison with `IsCircleConnectionForm` for
  `G = Circle`); in `Geometry/Manifold/FiberBundle/Associated/`:
  `Connection.lean` (the connection induced on $P\times_GF$, Exercise
  6.3.2); and `Geometry/Symplectic/Fibration/Associated.lean` (Weinstein's
  form: for a Hamiltonian action with equivariant moment map, in the
  page's sign `ω.IsEquivariantMomentMap (fun x ↦ -μ x)`, the form
  $\sigma+d\langle\mu,A\rangle$ on $P\times F$ equals
  $\pi_A^*\sigma+\langle\mu,F_A\rangle$, is closed, invariant and
  horizontal, so it descends to a closed form on $P\times_GF$ restricting
  to $\sigma$ along each fibre inclusion $x\mapsto[p,x]$; $F$ need not be
  compact).
- **Builds on:** Tau Ceti (principal and associated bundles, their
  fundamental fields and smooth structure, equivariant moment maps); the
  merged `Principal/BasicForm.lean` (basic forms descend) and
  `CircleConnection.lean`.
- **Milestones:** *Weinstein's universal construction for associated
  symplectic fibrations*, by the page's direct route.
- It uses Tau Ceti's moment map predicates as *Moment maps* states them
  and needs no file of *Lie group actions* or *Moment maps*, so it waits for
  no issue of `atlas/symplectic-group-actions.md`.
- **The design file decides:** how forms with values in `GroupLieAlgebra`
  are written (Tau Ceti's vector-valued `SmoothForm` or a basis), how
  $[A\wedge A]$ is formed, and how the descent along
  $P\times F\to P\times_GF$ is reduced to the merged descent along a
  principal bundle projection.

### 51. Integration over the fibre (needs `design/fiber-integration.md`)

- **Files:** in `Geometry/Manifold/DifferentialForm/FiberIntegral/`, the
  operator on a product in `Product/`, then on a fibration
  (for an oriented fibration with closed fibre of dimension $m$, the operator
  $\int_F\colon\Omega^j(M)\to\Omega^{j-m}(B)$,
  `TauCeti.MapFiber.Atlas.fiberIntegral`, defined in each chart and
  glued; its value in a trivialization; it commutes with $d$; the
  projection formula $\int_F(\pi^*\beta\wedge\alpha)=\beta\wedge\int_F\alpha$;
  naturality under pull-back along maps of the base; and, in degree $m$,
  the integral over each fibre).
- **Builds on:** *Symplectic fibrations* (only `StructureGroup.lean`, for
  oriented atlases); Tau Ceti (`integralTopForm`, orientations, Stokes's theorem on
  closed manifolds).
- **Milestones:** none; it serves *Coupling forms*. Later pages
  (characteristic classes of bundles, Gysin sequences) can use it.
- **The design file decides:** the sign convention for the fibre
  integral of a product (the page refers to Bott–Tu [BottTu1982]), and
  whether the fibre has to be closed or compactly supported forms are
  allowed.

### 52. Flux homomorphism (needs `design/flux-homomorphism.md`)

- **Files:** in Tau Ceti's folder `Geometry/Symplectic/Flux/`, beside the
  library's `Hamiltonian.lean` and `CompactSupport.lean`: `Kernel.lean`
  (on a closed connected symplectic manifold, a symplectic diffeotopy with
  zero flux ends in `TauCeti.SmoothForm.hamiltonianGroup`, and is
  homotopic with fixed ends to a Hamiltonian one: McDuff–Salamon, Theorem
  10.2.5, so that `TauCeti.endpointFlux` has kernel
  $\mathrm{Ham}$), `Countable.lean` (the flux group `TauCeti.fluxGroup` is
  countable, since the flux of a loop has periods among those of the
  symplectic form on integral 2-classes), and `Family.lean` (each smooth
  family in $\mathrm{Ham}$ has a time-dependent Hamiltonian generating it,
  McDuff–Salamon, Proposition 10.2.12).
- **Builds on:** the merged *Hamiltonian flows*; Tau Ceti
  (`TauCeti.Diffeotopy.flux`, `flux_trans`, `fluxGroup`, `endpointFlux`,
  `mem_ker_endpointFlux_iff`,
  `hamiltonianGroup_subgroupOf_le_ker_endpointFlux`).
- **Milestones:** none; it serves *Coupling forms* and *Hamiltonian
  fibrations*. These results are McDuff–Salamon's Chapter 10, which a later
  page may cover; they are built here as library results.
- **The design file decides:** the route to countability, and whether
  `Family.lean` and `Loop.lean` are needed by the routes that *Coupling
  forms* and *Hamiltonian fibrations* take.

### 53. Coupling forms (needs `design/coupling-forms.md`)

- **Files:** in `Geometry/Symplectic/Fibration/`: `Holonomy.lean`
  (holonomy of a symplectic connection read in a symplectic chart;
  contractible loops as boundaries of smooth discs; the holonomies along a
  smooth disc as a symplectic isotopy, the periods of whose velocity are
  computed from $d\tau$),
  `Curvature.lean` (the curvature identity
  $\iota(\Omega_\Gamma(v_1,v_2))\tau=d(\tau(v_1^\sharp,v_2^\sharp))-\iota(v_2^\sharp)\iota(v_1^\sharp)d\tau$
  on fibres; the local formula for $\Omega_\Gamma(\partial_i,\partial_j)$;
  and the equivalence of Hamiltonian holonomy around contractible loops,
  Hamiltonian curvature and exactness of $\partial_i\alpha_j-\partial_j\alpha_i$),
  `Coupling.lean` (the coupling form: existence of a closed connection
  two-form exactly under Hamiltonian holonomy around contractible loops,
  the normalization $\int_F\tau_\Gamma^{k+1}=0$, its equivalence with
  fibrewise mean value zero of $\tau_\Gamma(v_1^\sharp,v_2^\sharp)$, uniqueness, and
  $\tau=\tau_\Gamma+\pi^*\beta$) and `SimplyConnected.lean` (the corollary
  for a fibre with $H^1(F;\mathbb R)=0$).
- **Builds on:** *Symplectic fibrations*, *Parallel transport*,
  *Integration over the fibre*, *Flux homomorphism* (only `Family.lean`);
  *Compatible symplectic forms* (only `Thurston.lean`, for the corollary's
  second statement); the merged *Hamiltonian flows* (its criterion for
  Hamiltonian diffeotopies).
- **Milestones:** *Coupling form of a symplectic connection*, *Compatible
  symplectic forms for fibrations with simply connected fibre*, *Curvature
  identity for symplectic connections*.
- **The design file decides:** the proof of 2 ⇒ 1 (through the curvature,
  following Guillemin–Lerman–Sternberg, or in local coordinates with the
  normalization that the page corrects), and the form of the three facts
  that the book leaves as Exercises 6.4.4, 6.4.5 and 6.4.7, which the page
  says no source proves in full.

### 54. Hamiltonian fibrations (needs `design/hamiltonian-fibrations.md`)

- **Files:** in `Geometry/Symplectic/Fibration/`: `Hamiltonian.lean`
  (Hamiltonian connections and fibrations; a reduction of the structure
  group to $\mathrm{Ham}(F,\sigma)$; 1 ⇔ 2), `FluxHomomorphism.lean` (for a
  closed connection two-form on a fibration trivial over every loop, the
  homomorphism $f_\tau\colon H_1(B;\mathbb Z)\to H^1(F;\mathbb R)/\Gamma_\sigma$
  and its lifts) and `Characterization.lean` (the four
  conditions of Theorem 6.5.3 with the torsion condition, with 3 ⇒ 1 by a
  shift of the connection by closed one-forms of the base, with no
  triangulation); the homomorphism $\mu_{\Phi^*a}$ of a class over a
  trivialization over the 1-skeleton is in `OneSkeleton.lean`.
- **Builds on:** *Coupling forms*, *Flux homomorphism*, *Symplectic
  fibrations*, *Parallel transport*, *Compatible symplectic forms* (only
  `Thurston.lean`); Tau Ceti (singular homology; smooth triangulations,
  `Geometry/Manifold/SmoothTriangulation/`, only in `OneSkeleton.lean`).
- **Milestones:** *Characterization of Hamiltonian fibrations*, in the
  corrected form with the torsion condition, as the page states it.
- **The design file decides:** the meaning of a symplectic trivialization
  over the 1-skeleton (a trivialization over an open neighbourhood, as the
  page suggests), the reading of $H_1(B;\mathbb Z)$ and of torsion, and the
  steps of 3 ⇒ 1 that the book leaves to the reader.

### 55. Dehn twists (needs `design/dehn-twists.md`)

- **Files:** in `Geometry/Symplectic/DehnTwist/`: `Geodesic.lean` (the
  manifold $T=T^*S^n$ with coordinates in
  $\mathbb R^{n+1}\times\mathbb R^{n+1}$ and $d\lambda_{\mathrm{can}}$;
  the normalized geodesic flow as the Hamiltonian flow of $|p|$, from Tau
  Ceti's great circles `TauCeti.isGeodesicCurve_sphereGreatCircle`),
  `Model.lean` (the model twist for $R$ with
  $R(-t)=R(t)-t$, its smoothness across the zero section through
  Whitney's theorem on even functions, its support, $O(n+1)$-equivariance,
  the primitive $K$
  of $\tau^*\lambda-\lambda$, and the compactly supported Hamiltonian
  isotopy between two models, generated by $2\pi(R_1-R_0)(|p|)$),
  `Framing.lean` (framings of a Lagrangian sphere, as classes of
  parametrizations modulo isotopy and $O(n+1)$, with Tau Ceti's
  `TauCeti.orthogonalToDiffSphere`) and `Sphere.lean` (the twist along a
  framed Lagrangian sphere, its independence of the choices up to
  compactly supported symplectic isotopy, through uniqueness up to isotopy
  in the Lagrangian neighbourhood theorem, and its exactness).
- **Builds on:** the merged *Symplectic neighbourhoods*
  (`Neighborhood/Lagrangian.lean`), *Isotopy extension* and *Hamiltonian
  flows* (`Flux/CompactSupport.lean`); Tau Ceti (geodesics of the round
  sphere, the weak Whitney topology, isotopy classes of orthogonal maps of
  a sphere in `Geometry/Diffeomorphism/Sphere/Isotopy.lean`).
- **Milestones:** *Dehn twist along a framed Lagrangian sphere*. The
  remark that a Lagrangian 2-sphere has one framing, which uses Smale's
  theorem, is not part of the milestone, so the part does not wait for
  *Diffeomorphisms of the 2-sphere*.
- **The design file decides:** how $T$ is built (as a submanifold of
  $\mathbb R^{2n+2}$ or as Tau Ceti's cotangent bundle of the sphere with
  the sign change), the isotopy relation in the framing (smooth isotopies
  or paths in the weak Whitney topology), and the uniqueness of Lagrangian
  neighbourhoods, which the merged part proves only as existence.

### 56. Sphere bundles over surfaces (needs `design/sphere-bundles-over-surfaces.md`)

- **Files:** in `Geometry/Manifold/FiberBundle/SphereBundle/`:
  `Clutching.lean` (oriented $S^2$-bundles over a surface with boundary
  are trivial, and over a closed surface they are classified by the
  homotopy class of a clutching loop in $\mathrm{Diff}^+(S^2)$, with
  continuous homotopies made smooth) and `Classification.lean` (the two
  bundles, and $P\times_{S^1}S^2$ trivial exactly for even Euler number,
  with the circle bundles and Euler numbers of the merged *First Chern
  number*); and `Geometry/Symplectic/RuledSurface.lean` (the sections
  $B_k$, $H^2(X_B;\mathbb R)$ with the basis $b_\pm$ through a de Rham
  Leray–Hirsch theorem, the intersection numbers, and the three parts of the
  milestone: the necessary condition, the $S^1$-invariant form of
  Exercise 6.2.6, and the form on $\widetilde B\times_\rho S^2$ of Exercise
  6.2.9 for positive genus).
- **Builds on:** *Diffeomorphisms of the 2-sphere* (`ComplexStructure.lean`,
  `Mobius.lean` and `Trivialization.lean`, for `diffPlus` and the Möbius
  rotations, and `Smale.lean`, for $\pi_0$ and $\pi_1$); *Symplectic
  fibrations* (only `Basic.lean`, for oriented fibrations and compatible
  forms); *Principal connections* (only
  `Fibration/Associated.lean`, for the form of Exercise 6.2.6); the merged
  *First Chern number* and the library's de Rham cohomology.
- **Milestones:** *Classification of oriented 2-sphere bundles over
  surfaces*, by clutching; *Symplectic classes on the nontrivial 2-sphere
  bundle over a surface*.
- **The design file decides:** the models of $X_B$ that the constructions
  use and the isomorphisms between them, and how the coefficients
  $\mu_\pm$ are read (as the integrals of $a$ over $B_{\pm1}$, which
  avoids Poincaré duality in the statement), and how the singular
  Leray–Hirsch theorem is brought to de Rham classes.

## Dependencies and build order

Each part depends only on the parts listed, besides Mathlib and Tau Ceti.
A part's level counts only the parts whose unmerged work it waits for. A
part may also use files of a part at its own level or a higher one, provided
each such file is merged, as the notes in parentheses in the table record;
so two parts can each use merged files of the other without either waiting.
New imports of this kind are not recorded, and the notes here may fall
behind.

| Level | Part | Builds on |
|---|---|---|
| 0 | *Standard model* | — (it imports `LinearAlgebra/Matrix/Block.lean` and `LinearAlgebra/Matrix/Symmetric.lean` of *Siegel upper half space*, which import only Mathlib and Tau Ceti and are merged, `LinearAlgebra/Matrix/SymplecticGroup/Basic.lean` of *Symplectic group*, which imports only Mathlib and Tau Ceti and is merged, `LinearAlgebra/Matrix/PosDef/Block.lean` of *Siegel upper half space*, which imports only Mathlib and Tau Ceti and is merged, and the merged `LinearAlgebra/Symplectic/Compatible.lean` of *Compatible complex structures*, which besides `Standard/Basic.lean` imports only merged files that do not import `Standard/Matrix.lean`) |
| 0 | *Symplectic group* | — |
| 0 | *Linear Moser* | — (it imports `Topology/Algebra/Module/BilinearForm.lean` of *Compatible complex structures*, which imports only Mathlib and Tau Ceti and is merged) |
| 0 | *Smooth families* | — (`Diffeotopy/Real.lean` imports `Geometry/Diffeomorphism/Diffeotopy/Velocity.lean` of *Hamiltonian flows*, which is merged and imports no file of *Smooth families*) |
| 0 | *Cotangent bundles* | — |
| 0 | *Liouville structures* | — (it imports `Analysis/Calculus/ContDiff/Seeley/Extension.lean`, `Geometry/Manifold/LocalDiffeomorph/Basic.lean` and `Geometry/Manifold/MFDeriv/Chart.lean` of *Smooth families*, in `Geometry/Manifold/Boundary/Collar/Flow/Local.lean`, which are merged, `Geometry/Manifold/IsManifold/InteriorBoundary.lean` of *Symplectic vector bundles*, which is merged, `Geometry/Manifold/DifferentialForm/Smooth.lean` of *Moser isotopy*, which imports only Tau Ceti and is merged, and `Geometry/Symplectic/Manifold/Family.lean` of *Moser isotopy* and `Geometry/Manifold/DifferentialForm/SmoothFamily/Basic.lean` of *Smooth families*, in `StableHamiltonian.lean`, which are merged) |
| 0 | *Almost complex manifolds* | — (it uses only merged files of *Symplectic vector bundles*: `Symplectic/ComplexStructure/Basic.lean`, `Contractible.lean` and `ComplexStructure.lean`) |
| 0 | *Nijenhuis tensor* | — |
| 0 | *Lie group actions* | — |
| 0 | *Moment maps* | — |
| 0 | *Equivariant normal forms* | — (it uses only merged files of *Standard model*) |
| 0 | *Coisotropic reduction* | — (it uses only merged files of *Symplectic neighbourhoods* and `LinearAlgebra/Symplectic/Reduction.lean` of *Symplectic vector spaces*, which is merged) |
| 0 | *Hamiltonian reduction* | — |
| 0 | *Convexity* | — |
| 0 | *Kähler stability* | — |
| 0 | *Cauchy–Riemann operators on the sphere* | — (it uses only merged files of *Isothermal coordinates* and *Symplectic vector bundles*) |
| 0 | *Parallel transport* | — |
| 0 | *Principal connections* | — (it uses only merged files of *First Chern number*; no file of *Lie group actions* or *Moment maps*) |
| 0 | *Flux homomorphism* | — (it uses only merged files of *Hamiltonian flows*) |
| 0 | *Dehn twists* | — (it uses only merged files of *Symplectic neighbourhoods*, *Isotopy extension* and *Hamiltonian flows*) |
| 1 | *Unitary group topology* | *Symplectic group* (only the file on $\mathrm{Sp}(2n)$; the other files can start at once) |
| 1 | *Symplectic vector spaces* | *Standard model*, *Symplectic group* |
| 1 | *Lagrangian Grassmannian* | *Standard model*, *Symplectic vector spaces* (only `Subspace.lean`, which is merged) |
| 1 | *Linear nonsqueezing* | *Standard model* |
| 1 | *Linear complex structures* | *Standard model*; *Compatible complex structures* (only `LinearAlgebra/Symplectic/Compatible.lean`, which besides Mathlib and Tau Ceti imports only `LinearAlgebra/ComplexStructure/Action.lean` of this part, `Geometry/Symplectic/Darboux/EuclideanBasis.lean` of *Compatible complex structures* itself, which imports only Tau Ceti, `LinearAlgebra/Symplectic/Standard/Basic.lean` of *Standard model* and `LinearAlgebra/Symplectic/Subspace.lean` of *Symplectic vector spaces* (which in turn imports `LinearAlgebra/Matrix/SymplecticGroup/Basic.lean` of *Symplectic group*, which imports only Mathlib and Tau Ceti); all of them are merged. In turn, *Compatible complex structures* uses the merged `LinearAlgebra/ComplexStructure/Action.lean`, `Topology/ComplexStructure/Basic.lean`, `LinearAlgebra/ComplexStructure/Standard.lean` and `Topology/ComplexStructure/Orthogonal.lean` of this part, as its row lists) |
| 1 | *Siegel upper half space* | *Standard model*; *Lagrangian Grassmannian* (only `LinearAlgebra/Matrix/OfReal.lean`, which imports only Mathlib and Tau Ceti and is merged); *Linear complex structures* (only `LinearAlgebra/ComplexStructure/Action.lean`, which imports only Mathlib and Tau Ceti, `LinearAlgebra/ComplexStructure/Standard.lean`, which besides it imports only *Standard model*, `LinearAlgebra/Symplectic/Compatible.lean` of *Compatible complex structures* (which in turn imports, besides Mathlib and Tau Ceti, only `Action.lean`, `Geometry/Symplectic/Darboux/EuclideanBasis.lean` of *Compatible complex structures*, which imports only Tau Ceti, `LinearAlgebra/Symplectic/Standard/Basic.lean` of *Standard model* and `LinearAlgebra/Symplectic/Subspace.lean` of *Symplectic vector spaces*) and the library's `Geometry/Symplectic/Orientation.lean`, and that file, which imports only Tau Ceti; all of them are merged); *Symplectic group* (only `LinearAlgebra/Matrix/SymplecticGroup/Basic.lean`, which imports only Mathlib and Tau Ceti and is merged) |
| 1 | *Symplectic vector bundles* | *Standard model*, *Linear Moser*; its existence issue also the two `PolarComplexStructure/` issues of *Compatible complex structures*, its contractibility issue the Cayley domain issue of that part, and its homotopy-equivalence issue those three, none of which waits for another part |
| 1 | *Hamiltonian flows* | *Smooth families* (only `Diffeotopy/Real.lean`, for `SymplecticIsotopy.lean`, and `ContMDiff/TimeExtension.lean`, for `Flux/CompactSupport.lean`; the other files can start at once); `PoissonAlgebra.lean` imports `Geometry/Manifold/DifferentialForm/Flow/Family.lean` of *Contact geometry*, which besides Tau Ceti imports only `Geometry/Manifold/DifferentialForm/Pullback/Family.lean` of *Moser isotopy* and `Geometry/Manifold/DifferentialForm/SmoothFamily/Basic.lean` of *Smooth families*; all three are merged, so it can start at once |
| 1 | *Moser isotopy* | *Smooth families* (only `Stability.lean`; the other files can start at once); `Isotopy.lean` derives its theorem from `Moser/Family.lean` of *Isotopy extension* |
| 1 | *Isothermal coordinates* | *Nijenhuis tensor* (only `Integrable.lean`) |
| 1 | *Complex submanifolds* | *Nijenhuis tensor* |
| 1 | *Almost Kähler geometry* | *Almost complex manifolds* (only `Metric.lean`), *Nijenhuis tensor* (only `Covariant.lean` and `Nijenhuis.lean`); `TwoForm.lean` can start at once |
| 1 | *Space of compatible complex structures* | *Nijenhuis tensor* (only `Integrable.lean`), *Almost complex manifolds* (only `Metric.lean`); the merged *Siegel upper half space* and *Compatible complex structures* |
| 1 | *Energy of pseudoholomorphic curves* | *Almost complex manifolds* (only `Metric.lean`) |
| 1 | *Hodge theory* | *Nijenhuis tensor* (only `Integrable.lean`), *Almost complex manifolds* (only `Metric.lean`), each for one issue of its design file; the Hodge theorem for the Laplacian can start at once |
| 1 | *Hamiltonian circle actions* | *Lie group actions* (only `Circle.lean`), *Moment maps* (only `MomentMap/WeaklyHamiltonian.lean`); the nondegeneracy of the pairing can start at once |
| 1 | *Minimal coupling* | *Lie group actions* (only `Circle.lean`); merged files of *First Chern number* and *Smooth families* |
| 1 | *Equivariant localization* | *Lie group actions* (only `Circle.lean`), *Equivariant normal forms* (only `WeightModel/NormalForm.lean`); the Cartan complex can start at once |
| 1 | *Diffeomorphisms of the 2-sphere* | *Cauchy–Riemann operators on the sphere*; `ComplexStructure.lean` and `Mobius.lean` can start at once |
| 1 | *Symplectic fibrations* | *Parallel transport* (only for `Connection.lean` and `SymplecticFibres.lean`; `Basic.lean` and `LocalForm.lean` can start at once) |
| 2 | *Compatible complex structures* | *Standard model*, *Symplectic vector spaces*; *Linear complex structures* (only `LinearAlgebra/ComplexStructure/Action.lean`, which imports only Mathlib and Tau Ceti, `Topology/ComplexStructure/Basic.lean`, which besides it imports only Tau Ceti and the merged `LinearAlgebra/Matrix/NonsingularInverse.lean` and `Analysis/CStarAlgebra/Matrix.lean`, which import only Mathlib and merged files that do, and `LinearAlgebra/ComplexStructure/Standard.lean`, which besides `Action.lean` imports only `LinearAlgebra/Symplectic/Compatible.lean` of this part, `LinearAlgebra/Symplectic/Standard/Matrix.lean` of *Standard model*, the library's `Geometry/Symplectic/Orientation.lean`, which imports only Tau Ceti, and Tau Ceti; and `Topology/ComplexStructure/Orthogonal.lean`, which besides `Topology/ComplexStructure/Basic.lean` imports only `LinearAlgebra/Symplectic/Standard/Basic.lean` of *Standard model*, `Analysis/Matrix/Polar/Deformation.lean` of *Symplectic group* and Tau Ceti; all of them are merged); *Symplectic group* (only `LinearAlgebra/Matrix/SymplecticGroup/Basic.lean`, which imports only Mathlib and Tau Ceti and is merged, and `Analysis/Matrix/Polar/Deformation.lean`, through `Orthogonal.lean`, which is merged) |
| 2 | *Maslov index* | *Standard model*, *Symplectic group*, *Unitary group topology*; its Lagrangian issues also *Lagrangian Grassmannian* |
| 2 | *Isotopy extension* | *Hamiltonian flows* (only `DeRham/FamilyPrimitive.lean`, `Flux/Hamiltonian.lean` and `Flux/CompactSupport.lean`), *Smooth families* (only `ContMDiff/TimeExtension.lean`, `DifferentialForm/TimeExtension.lean` and `DeRham/SmoothFamily/GoodCover.lean`), *Moser isotopy* (only `Moser/Field.lean`); the merged *Standard model* and *Linear Moser*; the issues of its design file that use none of these can start at once |
| 2 | *Symplectic neighbourhoods* | *Moser isotopy* (only `Relative.lean`); *Symplectic vector spaces* (only `LinearAlgebra/Symplectic/Reduction.lean` and `LinearAlgebra/Symplectic/Subspace.lean`, which are merged); *Compatible complex structures* (only `LinearAlgebra/Symplectic/Compatible.lean`, which is merged); `CharacteristicFoliation.lean` and `AdaptedDarboux.lean` can start at once |
| 2 | *Complex projective space* | *Complex submanifolds* (only for the corollary in `Kahler.lean`; the other files can start at once) |
| 2 | *Compatible symplectic forms* | *Symplectic fibrations* (only `Basic.lean` and `HorizontalDistribution.lean`), *Minimal coupling* (only `RealChernClass.lean`); merged files of *Symplectic vector bundles*, *First Chern number*, *Moser isotopy* and *Smooth families* |
| 2 | *Integration over the fibre* | *Symplectic fibrations* (only `StructureGroup.lean`) |
| 2 | *Sphere bundles over surfaces* | *Diffeomorphisms of the 2-sphere* (`ComplexStructure.lean` for `DeRham/SphereBundle.lean`; up to `Trivialization.lean` for `SphereBundle/Basic.lean` and the files after it; `Smale.lean` for `Clutching.lean` and `Classification.lean`), *Symplectic fibrations* (only `Basic.lean`), *Principal connections* (only `Fibration/Associated.lean`, for `RuledSurface.lean`); `Smoothing.lean` can start at once |
| 3 | *First Chern number* | *Symplectic vector bundles*, the symplectic-loop issues of *Maslov index* |
| 3 | *Contact geometry* | *Smooth families* (only `Family.lean` and `Gray.lean`, through `ContMDiff/TimeExtension.lean`, `DifferentialForm/TimeExtension.lean` and `Diffeotopy/Real.lean`); *Symplectic neighbourhoods* (only `LegendrianNeighborhood.lean`, through `Lagrangian.lean`); *Moser isotopy* (only `Darboux/Strict.lean`, through `LocalDiffeomorph/MFDeriv.lean`, merged); the other files of the part can start at once |
| 3 | *Coupling forms* | *Symplectic fibrations*, *Parallel transport*, *Integration over the fibre*, *Flux homomorphism* (only `Family.lean`), *Compatible symplectic forms* (only `Thurston.lean`, for `SimplyConnected.lean`); in `Curvature.lean`, the curvature identity and the local curvature formula wait only for *Symplectic fibrations* and *Parallel transport* (`Curvature.lean`), and the equivalence also waits for `Holonomy.lean` and *Flux homomorphism* (`Family.lean`) |
| 4 | *First Chern class of nondegenerate forms* | *First Chern number* (only `FirstChernClass.lean`, #784); merged files of *Symplectic vector bundles*; `Geometry/Manifold/DifferentialForm/Pullback/Family.lean` of *Moser isotopy*, which is merged |
| 4 | *Adjunction* | *First Chern number* (only `FirstChernClass.lean`, `ChernNumber/Basic.lean` and `ChernNumber/Axioms.lean`); `NormalSpace/ComplexStructure.lean` and `NormalSplitting.lean` can start at once |
| 4 | *Chern classes* | *First Chern number* (only `FirstChernClass.lean`, for the comparison of $c_1$); the other issues of its design file can start at once |
| 4 | *Hamiltonian fibrations* | *Coupling forms*, *Flux homomorphism*, *Symplectic fibrations*, *Parallel transport*, *Compatible symplectic forms* (only `Thurston.lean`) |
| 5 | *Projective hypersurfaces* | *Chern classes*, *First Chern number* (only Poincaré duality, #810); the bundle isomorphisms on $\mathbb CP^{n+1}$, the normal bundle and the Lefschetz theorems can start at once |

The design issues of the parts marked as needing one can start at once, in
parallel with the level-0 parts.

## Milestones

### `atlas/linear-symplectic-geometry.md`

Every milestone of `atlas/linear-symplectic-geometry.md` except the deferred
*Gelfand–Robbin quotient (deferred)*. "Existing" means that a declaration at
the pinned Tau Ceti already proves it in full, so the library adds no
theorem; the close-out of #3 cites that declaration. Otherwise the part named
proves it, using what is listed in the part.

| Milestone | Where |
|---|---|
| *Linear Darboux theorem* | *Symplectic vector spaces*. Existing in part: the basis over any field and evenness are `LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J` and `LinearMap.BilinForm.IsAlt.even_finrank` (`LinearAlgebra/BilinearForm/SymplecticBasis.lean`); the real isomorphism is `TauCeti.SymplecticForm.exists_isSymplectomorphism_stdSymplecticForm_of_finrank_eq`. The library adds the isometry with `-stdSymplecticBilinForm k n` over any field and with `stdForm` over $\mathbb{R}$. |
| *Symplectic complements* | *Symplectic vector spaces*. Existing: `TauCeti.SymplecticForm.finrank_add_finrank_orthogonal`, `orthogonal_orthogonal`, `isSymplectic_orthogonal_iff`, `IsLagrangian.two_mul_finrank`, `IsIsotropic.isLagrangian_of_finrank` (`Geometry/Symplectic/Lagrangian/Basic.lean`). The library adds "isotropic if and only if the complement is coisotropic" and states the milestone as one theorem. |
| *Lagrangian extension lemma* | *Symplectic vector spaces*. Existing: `TauCeti.SymplecticForm.isLagrangian_iff_maximal_isIsotropic`, `LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J_inl_eq` (`LinearAlgebra/BilinearForm/LagrangianBasis.lean`). The library adds that every isotropic subspace lies in a Lagrangian one. |
| *Linear symplectic reduction* | *Symplectic vector spaces*. Existing: `TauCeti.SymplecticForm.reduction`, `reduction_mk`, `IsLagrangian.reduction_map` (`Geometry/Symplectic/LinearReduction.lean`), for $W/(W\cap W^\omega)$. The library adds the coisotropic statement and uniqueness. |
| *Nondegeneracy and the top exterior power* | Existing: `ContinuousAlternatingMap.wedgePow_ne_zero_iff` (`Geometry/Symplectic/Volume.lean`), for a two-form on a real space of dimension $2n$ given as a continuous alternating map (every alternating map on a finite-dimensional space is one). |
| *Unitary group as Sp ∩ O ∩ GL(n,C)* | Existing: `Matrix.symplecticGroup_inf_orthogonalGroup`, `Matrix.symplecticGroup_inf_centralizer_J`, `Matrix.orthogonalGroup_inf_centralizer_J` (`LinearAlgebra/Matrix/GeneralLinearGroup/Symplectic/Unitary.lean`) identify each pairwise intersection with the image of $\mathrm{U}(n)$ under realification, and the fact that any two of the three conditions imply the third holds for matrices over an arbitrary commutative ring by `SymplecticGroup.mem_iff_mem_orthogonalGroup_of_commute`, `SymplecticGroup.commute_J_of_mem_orthogonalGroup` (`LinearAlgebra/SymplecticGroup.lean`). |
| *Spectrum of a symplectic matrix* | *Symplectic group*. |
| *Symplectic polar decomposition and the maximal compact subgroup* | *Symplectic group*. Existing parts: `SymplecticGroup.rpow_mem` (`Analysis/Matrix/Polar/Symplectic.lean`), `TauCeti.GLSymplectic.maximal_isCompact_unitarySubgroup`, `Matrix.isPathConnected_symplecticGroup`, `TauCeti.GLSymplectic.polarHomotopy`; the right decomposition with uniqueness in a C*-algebra (`Units.polarUnitary_mul_sqrt_star_mul`, `Units.mul_eq_iff_polarUnitary_eq_and_sqrt_star_mul_eq`). The library adds that the positive factor is symplectic, that the polar homotopy is the book's $f_t$ and fixes $\mathrm{U}(n)$, so that it is a deformation retraction, and the homotopy equivalence. |
| *Fundamental group of the unitary group* | *Unitary group topology*: the isomorphisms for $n\ge1$ (see `ERRATA.md`), and, as a corollary, $\mathrm{SU}(n)$ simply connected for every $n$. Existing in part: the case $\mathrm{SU}(2)$, `Matrix.instSimplyConnectedSpaceSpecialUnitaryGroupFinTwoComplex`. |
| *Maslov index for loops of symplectic matrices* | *Maslov index*. Existing parts: `TauCeti.GLSymplectic.maslovIndex` with `maslovIndex_eq_of_homotopy`, `maslovIndex_mul`, `maslovIndex_sum`, `maslovIndex_scalarRotationLoop`. The library adds the converse of the homotopy axiom and uniqueness. |
| *Lagrangian frames and the Lagrangian Grassmannian* | *Lagrangian Grassmannian*. |
| *Maslov index for loops of Lagrangian subspaces* | *Maslov index*. |
| *Crossing-form formula for the Maslov index* | *Maslov index*. |
| *Maslov index for paths of Lagrangian subspaces* | *Maslov index*. |
| *Affine nonsqueezing theorem* | *Linear nonsqueezing*. |
| *Linear symplectic rigidity* | *Linear nonsqueezing*. |
| *Simultaneous normal form of a symplectic form and an inner product* | *Linear nonsqueezing*. The basis statement is Tau Ceti's Williamson theorem `TauCeti.SymplecticForm.exists_isDarbouxBasis_eq_sum_smul_elliptic_of_posDef` (`Geometry/Symplectic/Hamiltonian/Williamson.lean`); the library adds the ellipsoid consequences, uniqueness of the spectrum and the volume. |
| *Linear symplectic width of an ellipsoid* | *Linear nonsqueezing*. |
| *Linear complex structures are standard* | *Linear complex structures*. |
| *Characterizations of compatible complex structures* | *Compatible complex structures*. |
| *Contractibility of the space of compatible complex structures* | *Compatible complex structures*. Contractibility itself is existing: `TauCeti.SymplecticForm.instContractibleSpaceCompatible` (`Geometry/Symplectic/Cayley/Contractible.lean`). New here: on `StdSpace ι`, the compatible complex structures correspond to the symplectic matrices that are symmetric and positive definite, and the space of compatible structures is homotopy equivalent to $\mathrm{Met}(V)$, the inner products on $V$. |
| *Complex structures versus symplectic forms* | *Compatible complex structures*. |
| *Compact subgroups of the symplectic group* | *Compatible complex structures*. |
| *Contractibility of the space of tame complex structures* | *Compatible complex structures*. Contractibility is existing: `TauCeti.SymplecticForm.instContractibleSpaceTames`; the library adds that the inclusion of compatible structures is a homotopy equivalence. |
| *Linear Moser lemma* | *Linear Moser*. |
| *Siegel upper half space* | *Siegel upper half space*. |
| *Symplectic vector bundles are complex vector bundles* | *Symplectic vector bundles*. |
| *Compatible and tame complex structures on symplectic vector bundles* | *Symplectic vector bundles*, in the compact-open $C^0$ and $C^\infty$ topologies on sections (Tau Ceti's `ContMDiffSection.frameTopology`). |
| *Unitary trivializations over surfaces with boundary* | *Symplectic vector bundles*, with the surface connected, as the plan already corrects the book, and not assumed oriented. |
| *First Chern number of symplectic vector bundles over surfaces* | *First Chern number*, with the surface connected, as the plan already corrects the book. |
| *Chern–Weil formula for circle bundles over surfaces* | *First Chern number*, with the surface connected for the converse, as the plan notes. |
| *First Chern number as an Euler number* | *First Chern number*. |

The two milestones that are existing in full (*Nondegeneracy and the top
exterior power* and *Unitary group as Sp ∩ O ∩ GL(n,C)*) are cited with these
declarations in the close-out of #3, and need no issue; a milestone that Tau
Ceti proves only in part gets the rest from its part, which states the
milestone as one theorem with the plan's hypotheses and conclusion.

### `atlas/symplectic-manifolds.md`

Every milestone of `atlas/symplectic-manifolds.md`, and the milestone of
`auxiliary/smooth-primitives.md` that it needs. None is existing in full at
the pinned Tau Ceti: where Tau Ceti has a part, the row names it and the
part adds the rest and states the milestone as one theorem, in the page's
signs (*Manifolds, families and signs*) and with the page's hypotheses (for
instance properly embedded, not necessarily compact, submanifolds where Tau
Ceti assumes them compact).

| Milestone | Where |
|---|---|
| *Smooth families of primitives* (`auxiliary/smooth-primitives.md`) | *Smooth families*. Existing ingredients only: `TauCeti.homotopyOperator`, de Rham cohomology and its Mayer–Vietoris sequence. |
| *Symplectic vector fields and isotopy generators* | *Hamiltonian flows*. Existing parts: `TauCeti.SmoothTwoForm.mem_symplecticVectorFields_iff_mlieDerivForm_eq_zero`, `TauCeti.forall_mpullback_eq_iff_forall_mextDeriv_interior_eulerianField_eq_zero` (for all real times, applied to a `Diffeotopy` through its reading over `ℝ` in `Diffeotopy/Real.lean`), `TauCeti.SmoothTwoForm.isHamiltonianVectorField_mlieBracket` (with Mathlib's bracket). A jointly smooth family of diffeomorphisms over $[0,1]$ starting at the identity enters through the constructor of `Diffeotopy/OfContMDiff.lean`. |
| *Hamiltonian flows and the Poisson algebra* | *Hamiltonian flows*. Existing parts: `TauCeti.SmoothTwoForm.IsNondegenerate.isHamiltonianVectorField_iff_eq`, `TauCeti.SmoothTwoForm.IsHamiltonianVectorField.mpullback_flowOf_apply`, `TauCeti.SmoothTwoForm.IsHamiltonianVectorField.apply_eq_of_isMIntegralCurveOn`, `TauCeti.SmoothTwoForm.mpullback_timeDependentFlowOf_of_isHamiltonianVectorField`, `TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_jacobi`, `TauCeti.SmoothTwoForm.IsNondegenerate.hamiltonianVectorField_poissonBracket`, `TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_hamiltonianVectorField_comp`, `TauCeti.SmoothTwoForm.mem_ker_negHamiltonianLieHom_iff`, `TauCeti.SmoothTwoForm.range_negHamiltonianLieHom`. |
| *Hamiltonian isotopies and their composition* | *Hamiltonian flows*. Existing parts: `TauCeti.Diffeotopy.IsHamiltonian` and `HasHamiltonian` with `.trans`, `.symm` and `.transDiffeomorph`, `TauCeti.SmoothForm.hamiltonianGroup` with `mul_mul_inv_mem_hamiltonianGroup` and `normal_hamiltonianGroup_subgroupOf_diffeomorphStabilizer`. A jointly smooth family of diffeomorphisms over $[0,1]$ starting at the identity enters through the constructor of `Diffeotopy/OfContMDiff.lean`. |
| *Canonical cotangent structure and cotangent lifts* | *Cotangent bundles*. Existing parts: `TauCeti.CotangentBundle.liouvilleForm`, `mpullback_liouvilleForm`, `symplecticForm`, `inChartAt_liouvilleForm`, `inChartAt_symplecticForm_apply`, `Diffeomorph.mpullback_cotangent_liouvilleForm`, `Diffeomorph.mpullback_cotangent_symplecticForm`, `Diffeomorph.existsUnique_cotangent_eq_of_mpullback_liouvilleForm`. |
| *Moser stability* | *Moser isotopy*. Existing part: `TauCeti.SmoothTwoForm.exists_isotopy_mpullback_eq`, given primitives of the velocity. |
| *Relative Moser theorem with prescribed first derivative* | *Moser isotopy*. Existing part: the compact case, `TauCeti.SmoothTwoForm.exists_diffeomorph_opens_of_eq_along`. |
| *Darboux theorem with prescribed derivative* | *Moser isotopy*. Existing part: Darboux charts without the prescribed derivative, `TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart_of_symplecticForm`. |
| *Relative Moser theorem fixing a submanifold* | *Moser isotopy*. Existing part: the time-one map, `TauCeti.SmoothTwoForm.exists_diffeomorph_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub`, for a primitive vanishing as a full covector. |
| *Symplectic ball extension* | *Isotopy extension*. |
| *Symplectic isotopy extension* | *Isotopy extension*. |
| *Neighbourhood extension of submanifold isotopies* | *Isotopy extension*. |
| *Characteristic foliations and local symplectic quotients* | *Symplectic neighbourhoods*. Existing parts: `TauCeti.SmoothForm.isInvolutiveDistribution_ker_bilinFormAt`, `TauCeti.SmoothForm.characteristicFoliation`, `TauCeti.SmoothTwoForm.isSymplectic_descendedForm_iff`. |
| *Symplectic neighbourhood theorem* | *Symplectic neighbourhoods*. |
| *Lagrangian neighbourhood theorem* | *Symplectic neighbourhoods*. Existing input: `TauCeti.CotangentBundle.isLagrangianMap_zeroSection`. |
| *Isotropic neighbourhood theorem* | *Symplectic neighbourhoods*. |
| *Coisotropic neighbourhood theorem* | *Symplectic neighbourhoods*. |
| *Darboux charts adapted to submanifolds* | *Symplectic neighbourhoods*. |
| *Contact vector fields and contact Hamiltonians* | *Contact geometry*. Existing parts: `TauCeti.SmoothForm.IsContactForm.isContactHamiltonianVectorField_iff_eq`, `TauCeti.SmoothForm.IsContactHamiltonianVectorField.mlieDerivForm_eq`, `TauCeti.SmoothForm.IsContactForm.isContactHamiltonianVectorField_iff_mlieDerivForm`, `TauCeti.SmoothForm.IsContactForm.contactHamiltonianVectorField_one`. |
| *Contact Darboux theorem* | *Contact geometry*. Existing up to the change of coordinates $(q,p,z)\mapsto(q,-p,-z)$: `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart_of_finrank_eq`; for structures, `TauCeti.IsContactDistribution.exists_darbouxChart`. |
| *Gray stability* | *Contact geometry*. Existing part: `TauCeti.SmoothForm.grayDiffeomorph` with `mpullback_grayDiffeomorph_apply`, for coorientable families of forms over `ℝ`. |
| *Legendrian neighbourhood theorem* | *Contact geometry*. |
| *Contact-type hypersurfaces and Liouville collars* | *Liouville structures*. Existing parts: `TauCeti.IsContactType.isContactForm_mpullback`, `TauCeti.mpullback_flowOf_comp_apply_eq_symplectization`, `TauCeti.exists_continuous_pos_injOn_flowOf_comp`, `TauCeti.exists_pos_injOn_flowOf_comp`. |
| *Stable Hamiltonian structures and their neighbourhood model* | *Liouville structures*. Existing parts: `TauCeti.SmoothForm.IsStableHamiltonian`, `TauCeti.SmoothForm.characteristicVectorField` with `eq_characteristicVectorField_iff`. |
| *Completion of a strong filling* | *Liouville structures*. |

### `atlas/almost-complex-structures.md`

Every milestone of `atlas/almost-complex-structures.md` except the two
deferred ones, *Integrability theorem of Newlander–Nirenberg (deferred)* and
*Moduli spaces of simple J-holomorphic spheres (deferred)*. None is existing
in full at the pinned Tau Ceti; where Tau Ceti or the library has a part, the
row names it, and the part adds the rest and states the milestone as one
theorem in the page's conventions (*Almost complex structures, Kähler
manifolds and characteristic classes*).

| Milestone | Where |
|---|---|
| *Compatible and tame almost complex structures on manifolds* | *Almost complex manifolds*. Existing: the bundle statement `SymplecticGeometry.Bundle.contractibleSpace_compatible_tames` of *Symplectic vector bundles*, and Tau Ceti's `TauCeti.SmoothTwoForm.IsNondegenerate.exists_compatible`. |
| *First Chern class of a nondegenerate two-form* | *First Chern class of nondegenerate forms*, with the integral class of *First Chern number*. |
| *Levi-Civita derivative of a compatible almost complex structure* | *Almost Kähler geometry*. Existing inputs: Mathlib's `CovariantDerivative.leviCivitaConnection`, Tau Ceti's `CovariantDerivative.hom` and `TauCeti.SmoothForm.mextDeriv_apply_two`. |
| *Nijenhuis tensor* | *Nijenhuis tensor*. Existing parts: `TauCeti.SmoothAlmostComplexStructure.nijenhuis`, `nijenhuis_apply`, `nijenhuis_antisymm`, `nijenhuis_self`, `nijenhuis_apply_left`, `nijenhuis_apply_right`, `nijenhuis_eq_zero_of_finrank_eq_two`, `nijenhuis_const`, `isInvolutiveComplexDistribution_eigenspace_I_iff`. |
| *Parallel almost complex structures and the Kähler condition* | *Almost Kähler geometry*, with $N_J=0$ in condition 2, as the page asks. |
| *Integrability of almost complex structures on surfaces* | *Isothermal coordinates*. Existing inputs: `TauCeti.Beltrami.exists_isothermal_chart_finite_order` (planar charts of class $C^{k+1}$), `TauCeti.Beltrami.exists_centered_smooth_isothermal_chart` (smooth planar charts with smooth inverse). Missing: those charts read through the charts of a surface, `IsIntegrable` in real dimension two, and isothermal coordinates, built by the part. |
| *Fubini–Study form on complex projective space* | *Complex projective space*. Existing inputs: Tau Ceti's complex manifold `ℙ ℂ (Fin (n + 1) → ℂ)`, `TauCeti.SmoothTwoForm.existsUnique_isSymplectic_mpullback_eq`, `OnePoint.fubiniStudyForm`. |
| *Complex submanifolds of Kähler manifolds* | *Complex submanifolds*; its last sentence *Complex projective space*. Existing input: the linear `TauCeti.SymplecticForm.Compatible.restrict`. |
| *Kähler structure on the space of compatible linear complex structures* | *Space of compatible complex structures*. Existing inputs: `TauCeti.SymplecticForm.compatibleTangentSpace`, `TauCeti.SymplecticForm.Compatible.compatibleCayleyEquiv`, and the bijection with $\mathcal S_n$ of *Siegel upper half space*. |
| *Hodge decomposition on closed Kähler manifolds* | *Hodge theory*. Existing inputs: `TauCeti.harmonicForms` and its orthogonality results, `TauCeti.complexDeRhamCohomology`. |
| *Adjunction formula* | *Adjunction*; the example of plane curves *Projective hypersurfaces*. |
| *Chern classes of projective hypersurfaces* | *Projective hypersurfaces*, on *Chern classes*. Existing inputs: `TauCeti.isManifold_complexProjectiveZeroLocus`, `Projectivization.twistCore`, Tau Ceti's Lefschetz theorems in `Geometry/Manifold/Projectivization/Lefschetz.lean`. |
| *Energy identity for J-holomorphic curves* | *Energy of pseudoholomorphic curves*. Existing input: `TauCeti.integralTopForm_mpullback_nonneg`. |

The results that the page quotes rather than proves are handled as follows.
The integral first Chern class is *First Chern number*'s, the Euler class of
the determinant line. Higher Chern classes, the cohomology ring of
$\mathbb CP^n$ and the Euler characteristic formula are built by *Chern
classes*, Poincaré duality by *First Chern number*'s prerequisites
(#806–#810). The Hodge theorem is built by *Hodge theory*, on Tau Ceti's
elliptic regularity. *Energy of pseudoholomorphic curves* identifies
$\int_\Sigma u^*\omega$ with an evaluation on the image of the fundamental
class of $\Sigma$, if Tau Ceti has not done so by then. The integrability
theorem is used by no milestone. The
Lefschetz theorem is Tau Ceti's, whose remaining hypothesis *Projective
hypersurfaces* supplies. The signature theorem is not built: the
hypersurface milestone takes it as a hypothesis for the signature and
$b^\pm$ only (see *Departures*). The page's formulas fail in degree zero,
where the hypersurface is empty; `ERRATA.md` has an entry for this.

**The deferred milestones.** The integrability theorem would say, on a
boundaryless manifold, that `IsIntegrable J` holds exactly when
`J.nijenhuis = 0`. The parts state with `IsKahler` and $N_J=0$ every result
whose proof needs no charts, and use `IsIntegrable` only where they do, so a
later proof of the theorem makes the book's forms corollaries without
restating anything. The moduli spaces of spheres need the energy and
$\bar\partial_J$ of *Energy of pseudoholomorphic curves*, which agree with
Tau Ceti's `IsPseudoholomorphic` and its transversality files, the number
$\langle c_1(\omega),A\rangle$ of *First Chern class of nondegenerate forms*,
and residual sets of $\mathcal J(M,\omega)$ in Tau Ceti's `frameTopology`,
which is the $C^\infty$ topology of the page on a closed manifold. No part
fixes a choice that would have to change for them.

### `atlas/symplectic-group-actions.md`

Every milestone of `atlas/symplectic-group-actions.md`; the page defers
only examples and exercises, which get no part. The statements are in the
page's conventions (*Group actions, moment maps and periods*). None is
existing in full at the pinned Tau Ceti; where Tau Ceti has a part, the row
names it, and the part adds the rest and states the milestone as one
theorem with the page's hypotheses.

| Milestone | Where |
|---|---|
| *Equivariant Darboux theorem and quadratic local moment maps* | *Equivariant normal forms*. Existing up to the translation of signs and periods: `TauCeti.SmoothTwoForm.IsSymplectic.exists_equivariant_darbouxChart` (`Geometry/Symplectic/Manifold/EquivariantDarboux.lean`), `TauCeti.SmoothTwoForm.IsMomentMap.exists_weightModelChart` (`Geometry/Symplectic/Hamiltonian/WeightModel/NormalForm.lean`). |
| *Equivariance and the obstruction to an equivariant moment map* | *Moment maps*. Existing parts: `TauCeti.SmoothTwoForm.momentCocycle` with `IsMomentMap.momentCocycle_eq`, `momentCocycle_mem_twoCocycle`, `momentCocycle_add_const`, `IsEquivariantMomentMap.momentCocycle_eq_zero`, `IsMomentMap.isEquivariantMomentMap_of_momentCocycle_eq_zero`. |
| *Frankel–Ono Hamiltonianity criterion* | *Hamiltonian circle actions*. Existing input: `TauCeti.SmoothTwoForm.interiorClass_eq_zero_iff`. |
| *Minimal coupling* | *Minimal coupling*, on the merged `SymplecticGeometry.IsCircleConnectionForm`. |
| *Regular coisotropic reduction* | *Coisotropic reduction*. Existing parts: `TauCeti.SmoothForm.isInvolutiveDistribution_ker_bilinFormAt`, `TauCeti.SmoothTwoForm.existsUnique_isSymplectic_mpullback_eq`. |
| *Marsden–Weinstein reduction* | *Hamiltonian reduction*. Existing parts, for a group acting properly on all of $M$: `ProperSMul.instIsManifoldOrbitRelQuotient`, `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isManifold_orbitRelQuotient`, `existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback`, `ker_mfderiv_quotientMk_levelSubMulAction` (`Geometry/Symplectic/Hamiltonian/Reduction/ReducedSpace.lean`). |
| *Reduction at a coadjoint orbit and the shifting construction* | *Hamiltonian reduction*. Existing parts: `Module.Dual.coadjointOrbitForm`, `isEquivariantMomentMap_coadjointOrbitForm`, `IsEquivariantMomentMap.isRegularValue_sub`, `isCoisotropicMap_fst_sub`, `IsMomentMap.mpullback_smul_eq_prod_leftInvariantKirillovForm`. |
| *Clean reduction of Lagrangian submanifolds* | *Coisotropic reduction*. Existing input: `TauCeti.SymplecticForm.IsLagrangian.reduction_map`. |
| *Convexity and connectedness of moment-map fibers* | *Convexity*. Existing parts: `TauCeti.SmoothTwoForm.IsMomentMap.range_subset_convexHull_image_fixedPoints`, `finite_image_fixedPoints`, `apply_eq_of_isPreconnected`, `TauCeti.finite_connectedComponents_fixedPoints_of_compactSpace`. |
| *Duistermaat–Heckman localization* | *Equivariant localization*. |
| *Kempf–Ness correspondence* | *Kähler stability*. |
| *Hilbert–Mumford numerical criteria* | *Kähler stability*. |

**Shared with `atlas/symplectic-fibrations.md`.** That page builds on
*Lie group actions* and *Moment maps*, and adds its parts beside them. Its
connections on principal bundles with any structure group are those of
*Principal connections*; this page needs only the circle case, which the library has
(`Geometry/Manifold/FiberBundle/Principal/CircleConnection.lean`).

### `atlas/symplectic-fibrations.md`

Every milestone of `atlas/symplectic-fibrations.md` except the deferred
*Symplectic classes on the nontrivial 2-sphere bundle over the 2-sphere
(deferred)*, which gets no part. The statements are in the page's
conventions (*Fibrations, connections and diffeomorphism groups*), with the
page's added hypotheses of a connected fibre and a connected base surface.
None is existing at the pinned Tau Ceti or Mathlib; the rows name the
existing inputs.

| Milestone | Where |
|---|---|
| *Fibrations with symplectic fibres are symplectic fibrations* | *Symplectic fibrations* (`SymplecticFibres.lean`), by parallel transport of *Parallel transport*. |
| *Thurston's theorem on symplectic fibrations* | *Compatible symplectic forms* (`Thurston.lean`, with step 1 in `ClosedExtension.lean`). Existing inputs of `ClosedExtension.lean`: `TauCeti.deRhamCohomology.map_eq_of_homotopy`, `SmoothPartitionOfUnity`. |
| *Chern class criterion for compatible symplectic forms* | *Compatible symplectic forms* (`ChernClass.lean`), on the de Rham class `realFirstChernClass` of *Minimal coupling* for the determinant line. |
| *Symplectic forms on surface bundles with fibre genus different from one* | *Compatible symplectic forms* (`Surface.lean`), with the parametric Moser argument of `Moser/Parameter.lean`. |
| *Classification of oriented 2-sphere bundles over surfaces* | *Sphere bundles over surfaces* (`Classification.lean`), from *Smale's theorem on the diffeomorphism group of the 2-sphere*. Existing input: `TauCeti.specialOrthogonalGroupFundamentalGroupMulEquiv`. |
| *Symplectic classes on the nontrivial 2-sphere bundle over a surface* | *Sphere bundles over surfaces* (`RuledSurface.lean`). |
| *Weinstein's universal construction for associated symplectic fibrations* | *Principal connections* (`Fibration/Associated.lean`). Existing inputs: `TauCeti.AssociatedBundle.contMDiffFiberBundle`, `TauCeti.SmoothTwoForm.IsEquivariantMomentMap`. |
| *Symplectic connections correspond to vertically closed 2-forms* | *Symplectic fibrations* (`Connection.lean`). Existing input: `TauCeti.mlieDerivForm_eq_interior_mextDeriv_add`. |
| *Dehn twist along a framed Lagrangian sphere* | *Dehn twists*, on the merged Lagrangian neighbourhood theorem `TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.exists_symplectomorphism_cotangent`. |
| *Coupling form of a symplectic connection* | *Coupling forms* (`Coupling.lean`), with *Flux homomorphism* for McDuff–Salamon, Proposition 10.2.12. |
| *Compatible symplectic forms for fibrations with simply connected fibre* | *Coupling forms* (`SimplyConnected.lean`), with Thurston's theorem of *Compatible symplectic forms*. |
| *Curvature identity for symplectic connections* | *Coupling forms* (`Curvature.lean`), with the countability of the flux group from *Flux homomorphism*. |
| *Characterization of Hamiltonian fibrations* | *Hamiltonian fibrations*. |

### `auxiliary/diffeomorphisms-of-the-2-sphere.md`

Both milestones, proved in full. Their parts wait for no part of
`atlas/symplectic-fibrations.md`; of that page's milestones, only the
classification of 2-sphere bundles waits for them.

| Milestone | Where |
|---|---|
| *Diffeomorphisms of the 2-sphere form a trivial principal bundle over the complex structures* | *Diffeomorphisms of the 2-sphere* (`Trivialization.lean`), with the operators of *Cauchy–Riemann operators on the sphere*. Existing inputs: `Diffeomorph.exists_coe_eq_smul`, `Diffeomorph.eq_refl_of_apply_zero_one_infty_eq_self`, `Continuous.index_eq_of_preconnectedSpace`, and the merged integrability theorem `TauCeti.SmoothAlmostComplexStructure.isIntegrable_of_finrank_eq_two`. |
| *Smale's theorem on the diffeomorphism group of the 2-sphere* | *Diffeomorphisms of the 2-sphere* (`Smale.lean`). Existing inputs: `TauCeti.orthogonalToDiffSphere`, `Diffeomorph.isTopologicalGroup`. |

## Departures from the plan's advice

- **Field of scalars.** The linear Darboux theorem is proved over any field,
  against `-stdSymplecticBilinForm k n` on `Fin n ⊕ Fin n → k`. The results
  about isotropic, coisotropic and Lagrangian subspaces are stated for Tau
  Ceti's real `TauCeti.SymplecticForm`, the only place where those
  predicates exist. Generalizing them to bilinear forms over a field, or
  `stdSymplecticBilinForm` from `Fin n` to an arbitrary index type, would
  change Tau Ceti, so it belongs to issues there, not here.
- **Reduction.** Tau Ceti's reduction quotients an arbitrary subspace $W$ by
  $W\cap W^\omega$. That covers the book's coisotropic case, which the library
  derives from it instead of building a second quotient.
- **Top exterior power.** $\omega^n$ is Tau Ceti's wedge power of a continuous
  alternating map, with value $n!$ on a Darboux basis, which the plan allows.
- **Loops.** Loops are paths on $[0,1]$ with equal ends, as in Tau Ceti, not
  maps from $\mathbb{R}/\mathbb{Z}$. The two are equivalent; the Maslov
  design file proves the comparison if a statement needs it.
- **Euclidean model.** All metric statements are made on `StdSpace ι`, never
  on a Lean product of two Euclidean spaces, since on the product a ball is a
  product of balls.
- **Topology on spaces of sections.** McDuff–Salamon do not say which
  topology the spaces of sections carry. The library states the bundle
  milestones twice, for continuous sections in the compact-open $C^0$
  topology and for smooth sections in the compact-open $C^\infty$ topology,
  both being Tau Ceti's `ContMDiffSection.frameTopology` (see *Symplectic
  vector bundles*): these are the topologies Tau Ceti already has, and the
  explicit fibrewise constructions, smooth in the structure, induce
  continuous maps for them by the lemma planned in `Section/Topology.lean`.
  The library does not use the Whitney topology: a continuous path in it
  changes a section only on a compact set, so over a non-compact base two
  structures that differ outside every compact set lie in different path
  components.
- **Proof routes.** The linear contractibility results go through the Cayley
  transform and the equivariant $J_{g,\omega}$, as Tau Ceti does; the bundle
  part applies Tau Ceti's canonical linear constructions at each point. For regular crossings
  the library uses Tau Ceti's signature results instead of Kato's selection
  theorem.
- **Signs on `atlas/symplectic-manifolds.md`.** By `auxiliary/02-signs.md`,
  Hamiltonian fields satisfy $\iota(X_H)\omega=-dH$, cotangent bundles carry
  $d\lambda_{\mathrm{can}}$, symplectizations $d(e^t\alpha)$, and a
  hypersurface of contact type gets $\iota(Z)\omega|_M$, on every page.
  `atlas/symplectic-manifolds.md` instead states its
  milestones in McDuff–Salamon's signs: $\iota(X_H)\omega=dH$,
  $\omega_{\mathrm{can}}=-d\lambda_{\mathrm{can}}$, $-d(e^s\alpha)$ and
  $-\iota(Y)\omega|_Q$. The library follows the milestones, which fix their
  own signs, and writes each of them with Tau Ceti's objects as the table of
  *Manifolds, families and signs* says. Tau Ceti agrees with the page on
  Hamiltonian vector fields, Poisson brackets and cotangent bundles, and with
  `auxiliary/02-signs.md` on symplectizations and contact type, so no new
  definition is needed in either case. A later page in the signs of
  `auxiliary/02-signs.md` writes its $X_H$ as
  `TauCeti.SmoothTwoForm.hamiltonianVectorField` applied to $-H$.
- **Neighbourhood models.** The page builds explicit models $K^*\oplus E$ for
  neighbourhoods of submanifolds of constant rank. The library proves the
  four neighbourhood theorems by the proof routes the page gives for them,
  through tubular maps and the relative Moser theorem, and builds no general
  model, since no milestone needs one (see *Symplectic neighbourhoods*).
- **Holomorphic Darboux theorem.** The page suggests proving the real and
  holomorphic Darboux theorems together, over $\mathbb{R}$ or $\mathbb{C}$.
  The holomorphic theorem is not a milestone, and the library proves only the
  real one, from Tau Ceti's real Moser machinery; a later issue may
  generalize it.
- **Surfaces.** For *Integrability of almost complex structures on
  surfaces* the page prefers the route through local existence of
  $J$-holomorphic discs. The library takes the Beltrami route instead.
  Tau Ceti now gives smooth planar isothermal charts, with smooth inverse
  (`TauCeti.Beltrami.exists_centered_smooth_isothermal_chart`), while for
  discs it has the $C^1$ step
  (`TauCeti.exists_fderiv_one_add_apply_fderiv_I_eq_zero_of_contDiffAt`);
  the disc route would still have to build a chart from a family of discs
  and prove that family smooth. *Isothermal coordinates* only reads Tau
  Ceti's planar charts through the charts of a surface. Local existence of
  $J$-holomorphic discs stays available for the later theory of curves.
- **Kähler.** The library's Kähler pairs are Tau Ceti's `IsKahler`, with
  $N_J=0$ in place of integrability, and the book's integrability is the
  separate predicate `IsIntegrable` (see *Almost complex structures, Kähler
  manifolds and characteristic classes*). This follows the page's advice to
  prove the parallel-$J$ criterion and the Kähler structure of
  $\mathcal J(V,\omega)$ without the integrability theorem.
- **Spaces of forms.** The page's first milestone needs a topology on
  two-forms. Tau Ceti has none on `SmoothTwoForm`, so the statements about
  spaces of forms are made on *Symplectic vector bundles*'
  `Bundle.ContMDiffTwoForm` of the tangent bundle, in the same compact-open
  $C^\infty$ topology as the structures.
- **The signature theorem.** *Chern classes of projective hypersurfaces*
  derives the signature and $b^\pm$ of a surface in $\mathbb CP^3$ from the
  Hirzebruch signature theorem, which the page quotes and which no page
  makes a milestone. The library proves the numbered parts, the Chern
  classes, the Euler characteristic and the Betti numbers, and states the
  signature and $b^\pm$ with the signature formula for the surface as a
  hypothesis; building the signature theorem would need cobordism or index
  theory, far beyond this page.
- **Betti numbers.** In the Hodge milestone they are dimensions of de Rham
  cohomology, since Tau Ceti has no de Rham theorem with singular
  cohomology; the book's use of the result, the first Betti number of the
  Kodaira–Thurston manifold, is computed in de Rham cohomology by Tau Ceti.
- **Signs on `atlas/symplectic-group-actions.md`.** This page uses the
  Hamiltonian sign of `auxiliary/02-signs.md` and the usual bracket, unlike
  `atlas/symplectic-manifolds.md`, and its circles have period one, unlike
  Tau Ceti's `Circle.exp` and weight model. The library adds no definition
  for either: it states the milestones with Tau Ceti's predicates applied
  to $-\mu$ and with the period-one generator $\xi_1$, as *Group actions,
  moment maps and periods* says.
- **Equivariant Darboux theorem.** The page builds the chart from an
  averaged metric and its exponential map. The library takes Tau Ceti's
  theorem, which composes Bochner's linearization with an equivariant
  Moser argument, the same two steps, and only translates its statement.
- **Marsden–Weinstein reduction.** The page derives the reduced manifold
  from regular coisotropic reduction. The library builds it as Tau Ceti
  does, by the quotient manifold theorem for the free proper action on the
  level, and proves the statements about characteristic leaves
  separately; so *Hamiltonian reduction* does not wait for *Coisotropic
  reduction*.
- **Frankel–Ono criterion.** The page identifies a class with the
  Poincaré dual of an orbit. The library shows instead that the integral of
  $\gamma(X)\,\omega^n$ vanishes for every closed one-form $\gamma$ when
  there is a fixed point, which needs only the nondegeneracy of the de Rham
  pairing in degrees $(1,2n-1)$ and no homology class of an orbit.
- **Proof routes on `atlas/symplectic-fibrations.md`.** Where the page
  offers two routes, the library takes: parallel transport for
  *Fibrations with symplectic fibres are symplectic fibrations*, since
  *Coupling forms* needs parallel transport anyway; the elementary
  route through families of area forms for surface bundles of genus
  different from one, so that no principal bundle with an
  infinite-dimensional structure group is built, at the price of a Moser
  argument that depends smoothly on a parameter in the base
  (`Geometry/Symplectic/Moser/Parameter.lean`); the direct verification
  for Weinstein's construction, which needs no reduction; and clutching for
  the classification of 2-sphere bundles, which needs Smale's theorem only
  for $\pi_0$ and $\pi_1$. The principal bundle with structure group
  $\mathrm{Symp}(F,\sigma)$, which the page calls motivation only, is not
  built.
- **Real Chern classes.** The page uses only the image of $c_1(\mathrm{Ver})$
  in real cohomology, which it identifies with de Rham cohomology. Tau
  Ceti maps de Rham classes to singular ones but has no de Rham theorem
  back, so the library builds the real class directly as a de Rham class by
  Chern–Weil, instead of taking the image of the integral class, and
  compares the two only over closed oriented surfaces, through Chern
  numbers.
- **Diffeomorphisms of the 2-sphere.** The library takes the proof through
  the bundle over complex structures that the auxiliary page proposes, with
  the page's variant of step 1 that uses only the standard sphere, the
  constancy of the Fredholm index and the zero count, since Tau Ceti has
  the index and the sections of $\mathcal O(1)$ but no Riemann–Roch for the
  operators $D_J$.
