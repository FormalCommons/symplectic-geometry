# Projective hypersurfaces

This is the detailed design of part 34 of `DESIGN.md`, *Projective
hypersurfaces*. It covers the milestone *Chern classes of projective
hypersurfaces* of `atlas/almost-complex-structures.md` and the example of
plane curves of *Adjunction formula*. Sources: McDuff–Salamon
[McDuffSalamon2017], Examples 4.4.3–4.4.5 and Exercise 4.4.6; Griffiths–Harris
[GriffithsHarris1978], Chapter 1, §1 (the line bundles $\mathcal O(k)$, the
Euler sequence) and Chapter 0, §2; J. Milnor, *Morse Theory*, Annals of
Mathematics Studies 51, Princeton (1963), §7, the proof of the Lefschetz
theorem that Tau Ceti formalizes, with Andreotti–Frankel
[AndreottiFrankel1959]; J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed.,
Theorem 6.24 (tubular neighbourhoods); A. Hatcher, *Algebraic Topology*,
§3.3 (Poincaré duality). The Chern classes are those of *Chern classes*
(`design/chern-classes.md`), whose sources are Bott–Tu [BottTu1982], §20, and
Milnor–Stasheff.

All statements about Tau Ceti and Mathlib below were checked against the
pinned versions, as for `DESIGN.md`. Tau Ceti paths are relative to
`.lake/packages/TauCeti/TauCeti/`, and paths of new files are under
`SymplecticGeometry/`.

## Setting and conventions

- **Projective space.** $\mathbb CP^{m}$ is `ℙ ℂ (Fin (m + 1) → ℂ)` with Tau
  Ceti's complex manifold structure, modelled on `𝓘(ℂ, Fin m → ℂ)`. The
  hypersurfaces live in $\mathbb CP^{n+1}$, that is `m = n + 1`, so that `n`
  is the complex dimension of the hypersurface, as on the page.
- **A smooth hypersurface of degree `d`** is the structure
  `SymplecticGeometry.SmoothProjectiveHypersurface n d` of issue 1: a
  polynomial `poly : MvPolynomial (Fin (n + 2)) ℂ` with
  `isHomogeneous : poly.IsHomogeneous d` and
  `smooth : ∀ L ∈ TauCeti.complexProjectiveZeroLocus (fun _ : Unit ↦ poly),
  ∃ i, MvPolynomial.eval L.rep (MvPolynomial.pderiv i poly) ≠ 0`. This is the
  page's hypothesis word for word: the zero set of a homogeneous polynomial
  whose differential does not vanish on it. Tau Ceti's
  `TauCeti.mulVec_surjective_jacobiMatrixAt_iff_exists_eval_pderiv_ne_zero`
  turns `smooth` into the surjectivity of the cone Jacobian that
  `TauCeti.isManifold_complexProjectiveZeroLocus` takes. The carrier `X` is
  that zero locus, with Tau Ceti's atlas
  `TauCeti.complexProjectiveZeroLocusChartedSpace` for `V = univ`, modelled
  on `𝓘(ℂ, Fin n → ℂ)`, the same type as the `Fin (n + 1 - Fintype.card Unit) → ℂ`
  that Tau Ceti gives, written in `simp` normal form. The inclusion is Tau Ceti's bundled
  embedding `TauCeti.complexProjectiveZeroLocusEmbedding`, written $\iota$.
  A structure, rather than three hypotheses on every statement, lets the
  atlas, the manifold structure and compactness be instances.
- **Bundles.** All bundles are complex vector bundles in Mathlib's sense
  (`[VectorBundle ℂ G E]`), the form `chernClass` takes: the tangent bundles
  `TangentSpace 𝓘(ℂ, _)` of the complex manifolds $\mathbb CP^{n+1}$ and `X`,
  Tau Ceti's `Projectivization.twistCore k` for $\mathcal O(k)$ (so the page's
  hyperplane bundle $H$, with fibre $\ell^*$, is `twistCore 1`, and
  `twistCore (-1)` is the tautological line), pull-backs `f *ᵖ E`, and Tau
  Ceti's normal bundle `f.isImmersion.NormalSpace` of the embedding $\iota$ over the
  field `ℂ` (`normalSpaceFiberBundle`, `normalSpaceVectorBundle` with
  `𝕜 = ℂ`, model `ℂ`).
- **Cohomology and $h$.** Chern classes are *Chern classes*' `chernClass` and
  `totalChernClass`, in `TopCat.integralCohomology` and in the ring
  `TopCat.EvenIntegralCohomology`. The page's $h$ is *Chern classes*'
  `Projectivization.hyperplaneClass`, which is $c_1$ of `twistCore 1` by
  `Projectivization.complexEulerClass_twistCore_one` (#1040), and
  $\iota^*h$ is `X.hyperplaneClass` (issue 8), its pull-back by
  `evenIntegralCohomologyMap`.
- **Orientation, fundamental class, numbers.** `X` is oriented by its complex
  structure, Tau Ceti's `TauCeti.complexManifoldOrientation`, and
  $[X]$ and $\langle c,[X]\rangle$ are Tau Ceti's
  `HomologicalOrientation.fundamentalClass` and `evalFundamentalClass` for
  its `toHomologicalOrientation`, as `DESIGN.md` says. This needs `n ≠ 0`:
  Tau Ceti's homological orientations are of positive dimension. The Euler
  characteristic is Tau Ceti's `TauCeti.eulerChar`, under the instance
  `SmoothProjectiveHypersurface.instFiniteCWType`, Tau Ceti's
  `TauCeti.ComplexManifold.finiteCWType` for `X`. Betti numbers are
  `TauCeti.bettiNumber ℚ X k`, the dimension of $H_k(X;\mathbb Q)$, so the
  rank of $H_k(X;\mathbb Z)$ as `DESIGN.md` asks.
- **The intersection form and the signature.** For a
  closed oriented four-manifold, the intersection form over `ℚ`,
  `TauCeti.HomologicalOrientation.intersectionForm`, is Tau Ceti's
  cup pairing `TopCat.singularCupPairing ℚ (h : 2 + 2 = 4) μ` on
  $H^2(X;\mathbb Q)$ (`AlgebraicTopology/Cohomology/Cap/Kronecker.lean`),
  with `μ` the rational fundamental class, the library's
  `TopCat.singularHomologyIntToRat 4 (oₕ.fundamentalClass _)`
  (`AlgebraicTopology/Cohomology/Cap/RationalCoefficients.lean`). The numbers
  $b^\pm$ are the indices of inertia `sigPos` and `sigNeg` of its quadratic
  form `TauCeti.HomologicalOrientation.intersectionQuadraticForm` (Mathlib's
  `LinearAlgebra/QuadraticForm/Signature.lean`, at the pin in the root
  namespace), and the signature `TauCeti.HomologicalOrientation.signature` is
  $b^+-b^-$; this is how Tau
  Ceti's `AlgebraicTopology/Cohomology/Sphere/IntersectionForm.lean` reads
  $b_2^+$. Over `ℚ` the indices agree with those over `ℝ` (Sylvester), and
  `ℚ` is the field over which the library has Poincaré duality.

## Decisions

`DESIGN.md` leaves four questions to this file.

### The hypothesis of Tau Ceti's Lefschetz theorems

Tau Ceti's theorems in `Geometry/Manifold/Projectivization/Lefschetz.lean`
(`TauCeti.isIso_homologyMap_notMem_affineOpen`,
`TauCeti.bijective_homotopyGroupMap_notMem_affineOpen`,
`TauCeti.joined_notMem_affineOpen_iff`) are about a closed set $Y$ of
$\mathbb CP^N$ and a coordinate hyperplane $\{x_i=0\}$. They assume that
the affine part of $Y$ is a complex manifold immersed holomorphically in
$\mathbb C^N$, and that $Y\cap\{x_i=0\}$ has a neighbourhood $W$ in $Y$ whose
inclusion is a weak homotopy equivalence (or a homology isomorphism).
$M$ is not a hyperplane section of $\mathbb CP^{n+1}$, so the theorems are
applied through the Veronese embedding, as the book does:

- Tau Ceti's `Projectivization.veroneseLinearForm d p` is a linear form on
  the space of monomials of degree `d`, and
  `Projectivization.preimage_veronese_complexProjectiveZeroLocus_veroneseLinearForm`
  says that the Veronese map pulls its zero set back to the zero set of `p`.
  Choose a linear equivalence of the space of monomials with
  `Fin (N + 1) → ℂ` whose coordinate `0` is that form (`p ≠ 0`, since `X`
  is a smooth hypersurface, so the form is nonzero). Composed with it, the
  Veronese map $v$ is a closed holomorphic embedding
  (`Projectivization.isSmoothEmbedding_map_comp_veronese`,
  `Projectivization.isClosedEmbedding_map_comp_veronese`, for `d ≠ 0`), and
  $Y=v(\mathbb CP^{n+1})$ meets $\{x_0=0\}$ exactly in $v(X)$.
- The affine part of $Y$ is the image of the open set
  $\mathbb CP^{n+1}\setminus X$, which is a complex manifold of dimension
  $n+1$; its charts are carried to $Z=$ `affineChart 0 '' (Y ∩ affineOpen 0)`
  by the homeomorphism `affineChart 0 ∘ v`, and the inclusion of $Z$ in
  $\mathbb C^{N}$ is then `affineChart 0 ∘ v` read in those charts, which is
  holomorphic, with injective differential since $v$ is an immersion
  (`Projectivization.isImmersion_map_comp_veronese`).
- The neighbourhood is a tubular one. Tau Ceti's
  `TauCeti.SmoothEmbedding.exists_homotopyEquiv_subset`
  (`Geometry/Manifold/TubularNeighborhood/Existence.lean`) gives an open
  neighbourhood of $\iota(X)$ in $\mathbb CP^{n+1}$ onto which $\iota$ is a
  homotopy equivalence. It is stated for real models, so $\iota$ is read as a
  real embedding by `TauCeti.SmoothEmbedding.restrictScalars`
  (`Geometry/Manifold/SmoothEmbedding/RestrictScalars.lean`).
  Its image under $v$ is the $W$ wanted: a homotopy equivalence is a weak
  homotopy equivalence (`ContinuousMap.HomotopyEquiv.isWeakHomotopyEquivalence`)
  and induces isomorphisms on homology.

So no new neighbourhood theorem is needed: the hypothesis is discharged for
every smooth hypersurface of positive degree. The affine part has complex
dimension $n+1$, so for $k+1<n+1$ the inclusion $X\to\mathbb CP^{n+1}$
induces isomorphisms on $\pi_k$ and on $H_k(\,\cdot\,;R)$. This gives what
the milestone uses: $X$ is connected for $n\ge1$, simply connected for
$n\ge2$ (Tau Ceti's `ComplexProjectiveSpace.instSimplyConnectedSpace`,
through `homeomorphProjectivization`), and $b_k(X)=b_k(\mathbb CP^{n+1})$
for $k<n$ (Tau Ceti's `ComplexProjectiveSpace.singularHomologyIso` and
`isZero_singularHomology_of_odd`). Poincaré duality gives the degrees above
$n$, and the Euler characteristic the middle one.

### The normal bundle, and no descended structure

The page's cleaner route is taken: $\nu_X\cong\iota^*\mathcal O(d)$ through
the derivative of the polynomial. At a point of `X` in the affine open
`U_i`, Tau Ceti's `TauCeti.complexProjectiveZeroLocusNormalSpaceEquiv`
identifies the normal space with `Unit → ℂ` by the differential of the
dehomogenized polynomial, which is the coordinate of `twistCore d` in chart
`i`. On an overlap, the dehomogenizations differ by the factor
$(v_i/v_j)^d$, so at a zero their differentials differ by that factor, which
is `twistTransition d i j`: the pointwise maps assemble to one fibrewise
isomorphism.

Tau Ceti builds the normal bundle of an embedding over any complete
nontrivially normed field (`NormalSpace/VectorBundle/Basic.lean`). For the
holomorphic embedding $\iota$, with `𝕜 = ℂ`, it is already a complex vector
bundle, and its multiplication by `i` is the one of the tangent spaces. So
this part does not use *Adjunction*'s
`Geometry/Manifold/SmoothEmbedding/NormalSpace/ComplexStructure.lean`, which
the reviews of #838 and #893 expected it to import, nor its $J$-invariance
hypothesis `hJ`. That file descends an almost complex structure $J$ of a real
manifold to the real normal bundle; using it here would mean reading
$\mathbb CP^{n+1}$ as a real manifold with
`SmoothAlmostComplexStructure.ofComplexManifold`, taking its real normal
bundle, and comparing the result with the complex bundles in which every
other class of the part is computed. No milestone needs that comparison.
The genus of plane curves is not derived from `adjunction_formula` either
(below), so *Adjunction* is not a prerequisite.

The tangent bundle of `X` and the normal bundle are compared with
$\iota^*T\mathbb CP^{n+1}$ by a splitting of the exact sequence
$0\to TX\to\iota^*T\mathbb CP^{n+1}\to\nu\to0$, built from a fibrewise right
inverse of the quotient map. Near each point, a complement of the image of
the differential fixed in a tangent chart gives a linear one (Tau Ceti's
`TauCeti.SmoothEmbedding.normalSpaceEquivOfComplement`, over any field);
fibrewise linear right inverses form an affine space, so a partition of unity
glues them. The splitting is general (issue 4), and complex linear for
`𝕜 = ℂ`. *Adjunction*'s `normalSplitting` is the inverse of the same
isomorphism, for the right inverse into the symplectic complement of a
compatible form.

### $\langle\iota^*h^n,[X]\rangle=d$ by counting points on a line

The book pairs with a line; no Poincaré dual of a zero locus is available
in the libraries. The class $\iota^*h^n$ is the Euler class of
$\iota^*\mathcal O(1)^{\oplus n}$ (by `chernClass_finrank_eq_complexEulerClass`
and the total Chern class of issue 6). A tuple $(\ell_1,\dots,\ell_n)$ of
linear forms is a holomorphic section of it whose zeros are the points of
$X$ on the projective line $\{\ell_1=\dots=\ell_n=0\}$. Then:

- Tau Ceti's `ContMDiffSection.mem_residual_setOf_regular_and_finite_zero_affineFamily`
  (`Geometry/Manifold/VectorBundle/Section/Generic.lean`), for the real
  family spanned by the sections $x_j e_k$ and $\mathrm i\,x_j e_k$, which
  span every fibre, gives tuples whose section is transverse to zero with
  finitely many zeros. These form a residual set; the tuples of independent
  forms are open and dense, so some tuple has both properties.
- At a transverse zero the derivative of the section is complex linear and
  invertible, so in a holomorphic chart and a complex trivialization its real
  determinant is positive (Tau Ceti's `Analysis/Complex/Determinant.lean`),
  and Tau Ceti's `TauCeti.VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt`
  makes each index $+1$. By
  `TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex`
  the number is the count of zeros.
- The count is $d$ (issue 9): the line is the image of an injective linear
  map $\iota:\mathbb C^2\to\mathbb C^{n+2}$, and the polynomial pulled back
  along $\iota$ (by `aeval` of Mathlib's `Matrix.toMvPolynomial`, as in Tau
  Ceti's `TauCeti.preimage_map_complexProjectiveZeroLocus`) is a binary form
  of degree $d$. Transversality at a point of the line says that this form's
  gradient is nonzero there (the tangent space of `X` is the kernel of the
  differential, Tau Ceti's
  `TauCeti.tangentRange_complexProjectiveZeroLocusEmbedding`), so it has no
  squared linear factor. By Tau Ceti's
  `MvPolynomial.IsHomogeneous.exists_linear_factors` it is then a product of
  $d$ pairwise non-proportional linear forms, each with one zero on
  $\mathbb CP^1$ (`LinearAlgebra/Projectivization/BinaryForm.lean`).

For `n = 0`, Tau Ceti's fundamental classes need positive dimension, so
the pairing with $[X]$ is read as a count of points: part 2 of the milestone
says that $X$ consists of $d$ points, and issue 9 proves `Nat.card X = d`.
Part 4 for `n = 0` is a statement about $\chi(X)$, so issue 9 also proves
`TauCeti.eulerChar X = d`. $X$ is a compact manifold of dimension $0$,
hence finite and discrete; its `FiniteCWType` instance is Tau Ceti's
`TauCeti.FiniteCWType.of_discreteTopology`, from the instances
`DiscreteTopology X` and `Finite X` of issue 9, and Tau Ceti's
`TauCeti.eulerChar_of_discreteTopology` turns `Nat.card X = d` into
$\chi(X)=d$.

### Where the signature theorem enters

As `DESIGN.md` decided (*Departures*), the Hirzebruch formula is a
hypothesis: for a surface, the statement of $\sigma$ and $b^\pm$ assumes
$3\sigma=\langle c_1^2-2c_2,[X]\rangle$, written with `signature`,
`integralCup` and `evalFundamentalClass`. From it and the Chern numbers,
$3\sigma=(4-d^2)d$. The relation $b^++b^-=b_2$ is proved, not assumed: the
cup pairing is nondegenerate, by Tau Ceti's
`TopCat.nondegenerate_singularCupPairing_iff` and the library's
`TauCeti.HomologicalOrientation.bijective_singularCapLinearMap_fundamentalClass`
(from Poincaré duality, #810), so Tau Ceti's
`QuadraticForm.sigPos_add_sigNeg_of_nondegenerate` applies, and
$\dim H^2(X;\mathbb Q)=b_2$ by Tau Ceti's
`TopCat.finrank_singularCohomology`.

### Degree zero

The structure allows `d = 0`: then `poly` is a nonzero constant and `X` is
empty. Parts 1–4 of the milestone hold for it, and so do the formulas for
the Chern classes, $\chi$ and $\sigma$, but the page's formulas for the
Betti numbers, $b^\pm$ and the genus do not (for surfaces they would give
$b_2=-2$). The statements of issues 14 and 15 assume `d ≠ 0` only for the
Betti numbers, $b^\pm$ and the genus, and the issue that states them adds an entry to
`ERRATA.md` with the empty surface as the counterexample.

## Files

The hypersurface files are in `Geometry/Manifold/Projectivization/Hypersurface/`,
as in `DESIGN.md`, beside Tau Ceti's `ZeroLocus.lean` (Tau Ceti has no file
`Hypersurface.lean` there). Three files are about projective space itself and
sit beside Tau Ceti's `LineBundle.lean`, in that folder (not in a folder
`LineBundle/`, since Tau Ceti has a file of that name there); the splitting
is general and sits beside Tau Ceti's `NormalSpace/` files, as *Adjunction*'s
`NormalSpace/ComplexStructure.lean` does; the Euler characteristic of a compact
complex manifold sits beside Tau Ceti's
`Geometry/Manifold/Complex/Orientation.lean`; Poincaré duality for
Betti numbers is an addition to the library's file of rational coefficients.
The pointwise continuity of fibrewise operations is general too:
`Topology/VectorBundle/Section.lean`
complements Tau Ceti's file of that path, as the library's `Pullback.lean`
there does. None of the other names is taken by Tau Ceti at the same place.
The list is in the order of the paths.

| File | Contents | Issue |
|---|---|---|
| `Algebra/Module/LinearMap/Polynomial.lean` | differentiating the linear forms of `Matrix.toMvPolynomial` | 9 |
| `AlgebraicTopology/Cohomology/Cap/RationalCoefficients.lean` (addition) | Poincaré duality for rational Betti numbers | 13 |
| `AlgebraicTopology/Singular/HomologyMap.lean` | homology isomorphisms across a commutative square | 12 |
| `Geometry/Manifold/Complex/EulerCharacteristic.lean` | real and complex tangent bundles of a complex manifold; $\chi=\langle c_{top},[M]\rangle$ | 7 |
| `Geometry/Manifold/Instances/Projectivization.lean` | the derivatives of the transition maps of projective space | 3 |
| `Geometry/Manifold/Projectivization/ChernClass.lean` | $c(\mathcal O(k))$, $c(\mathcal O(k)^{\oplus r})$, $c(T\mathbb CP^m)$ | 6 |
| `Geometry/Manifold/Projectivization/EulerSequence.lean` | $T\mathbb CP^m\oplus\mathbb C\cong\mathcal O(1)^{\oplus(m+1)}$ | 3 |
| `Geometry/Manifold/Projectivization/Hypersurface/Basic.lean` | the structure, its manifold structure, the Fermat hypersurfaces | 1 |
| `Geometry/Manifold/Projectivization/Hypersurface/BettiNumber.lean` | the Betti numbers | 14 |
| `Geometry/Manifold/Projectivization/Hypersurface/ChernClass.lean` | $\iota^*h$, $c_1(\nu)$, $c(TX)$ | 8 |
| `Geometry/Manifold/Projectivization/Hypersurface/Degree.lean` | $\langle\iota^*h^n,[X]\rangle=d$ | 10 |
| `Geometry/Manifold/Projectivization/Hypersurface/EulerCharacteristic.lean` | $\chi(X)$ | 11 |
| `Geometry/Manifold/Projectivization/Hypersurface/Lefschetz.lean` | the Lefschetz theorems for $X$ | 12 |
| `Geometry/Manifold/Projectivization/Hypersurface/Line.lean` | a transverse line meets $X$ in $d$ points | 9 |
| `Geometry/Manifold/Projectivization/Hypersurface/NormalBundle.lean` | $\nu\cong\iota^*\mathcal O(d)$ | 5 |
| `Geometry/Manifold/Projectivization/Hypersurface/PlaneCurve.lean` | the genus of a plane curve | 15 |
| `Geometry/Manifold/Projectivization/Hypersurface/Surface.lean` | surfaces in $\mathbb CP^3$ | 15 |
| `Geometry/Manifold/Projectivization/Hypersurface/Threefold.lean` | threefolds in $\mathbb CP^4$ | 15 |
| `Geometry/Manifold/Projectivization/Hypersurface/Veronese.lean` | $X$ as a hyperplane section of the Veronese image | 12 |
| `Geometry/Manifold/Projectivization/TwistCore.lean` | sums and tensor products of the bundles $\mathcal O(k)$ | 2 |
| `Geometry/Manifold/SmoothEmbedding/NormalSpace/Splitting.lean` | $TM\oplus\nu\cong f^*TN$ | 4 |
| `Geometry/Manifold/SmoothEmbedding/RestrictScalars.lean` | a holomorphic embedding is a real smooth embedding | 12 |
| `LinearAlgebra/Pi/LinearForm.lean` | a nonzero linear form as a coordinate of an automorphism | 12 |
| `LinearAlgebra/Projectivization/BinaryForm.lean` | a binary form with simple zeros has `d` zeros on $\mathbb CP^1$ | 9 |
| `LinearAlgebra/Projectivization/HermitianProjector.lean` | the Hermitian projector in the standard affine charts | 3 |
| `LinearAlgebra/Projectivization/VeroneseLinearForm.lean` | the linear form of a nonzero homogeneous polynomial is nonzero | 12 |
| `Topology/ComplexProjectiveSpace/SimplyConnected.lean` | `ℙ ℂ V` is simply connected | 12 |
| `Topology/Homotopy/HomotopyGroup/ConnectedMap/PathConnected.lean` | path-connectedness under `n`-connected maps | 12 |
| `Topology/VectorBundle/Section.lean` | pointwise continuity of fibrewise scalar multiples and finite sums | 4 |

### `Geometry/Manifold/Projectivization/Hypersurface/Basic.lean`

Namespace `SymplecticGeometry`.

- `SmoothProjectiveHypersurface n d`, the structure above, with
  `@[ext]` on `poly`. `X.carrier : Set (ℙ ℂ (Fin (n + 2) → ℂ))`, the zero
  locus, with `mem_carrier_iff`, and a `CoeSort` to its subtype.
- Instances on the carrier: `ChartedSpace`, from Tau Ceti's
  `complexProjectiveZeroLocusChartedSpace` with `V = univ`;
  `IsManifold 𝓘(ℂ, _) ω` (`isManifold_complexProjectiveZeroLocus`);
  `CompactSpace` (closed in a compact space,
  `isClosed_complexProjectiveZeroLocus`) and `T2Space`.
- `X.surjective_jacobiMatrixAt`, the cone-Jacobian form of `smooth`;
  `X.embedding`, Tau Ceti's `complexProjectiveZeroLocusEmbedding` for
  regularity `ω`, `@[expose]` so that Tau Ceti's lemmas about that embedding apply
  to it by definitional unfolding (`exact`, `erw`; not `rw` or `simp`, since
  they are stated on the general model), with
  `coe_embedding : ⇑X.embedding = Subtype.val`.
- `X.poly_ne_zero`, and `X.nonempty` for `d ≠ 0` (a homogeneous polynomial
  of positive degree in at least two variables has a nonzero zero over `ℂ`).
- `fermat n d`, the hypersurface $\sum_j z_j^d=0$ of the book,
  with `fermat_poly`: its partial derivatives are $d z_j^{d-1}$, and some
  coordinate of a point is nonzero. It is the example the structure needs.

### `Geometry/Manifold/Projectivization/TwistCore.lean`

Namespace `Projectivization`, over a field `𝕜` as Tau Ceti's `twistCore`
where nothing else is needed, and over a complete one for the continuity of
the tensor products on total spaces.

- `twistPiCore k ι`, the vector bundle core of $\mathcal O(k)\otimes\mathbb
  C^\iota$, with model `ι → 𝕜` and coordinate change
  `twistTransition k i j x • id`, with `twistPiCore_coordChange_apply`, and
  its `IsContMDiff` instance, as for `twistCore`.
- `twistPiCoreOptionEquiv k ι x`: the fibrewise linear equivalence
  `(twistPiCore k (Option ι)).Fiber x ≃L[𝕜] ((twistCore k).Fiber ×ᵇ
  (twistPiCore k ι).Fiber) x` (by `ContinuousLinearEquiv.piOptionEquivProd`
  of Tau Ceti's `Topology/Algebra/Module/Equiv/Pi.lean`), continuous on
  total spaces in both directions; and, for `IsEmpty ι`,
  `twistPiCoreTrivializationOfIsEmpty`, a global trivialization of the
  rank-zero `twistPiCore k ι`. These make $\mathcal O(k)^{\oplus r}$ an
  iterated direct sum for the Whitney formula.
- `twistCoreTensorEquiv k l x`: the fibrewise equivalence
  `(twistCore (k + l)).Fiber x ≃L[𝕜] (twistCore k).Fiber x ⊗[𝕜]
  (twistCore l).Fiber x`, `a ↦ a ⊗ 1` in each chart, derived from
  `ScalarCocycle.lineBundleCoreTensorEquiv`, continuous on total spaces for Tau
  Ceti's tensor product bundle (`Topology/VectorBundle/TensorProduct/Basic.lean`);
  and `twistCoreZeroTrivialization`, the trivialization of `twistCore 0`
  (`twistTransition_zero`). #1040 uses the case `k = 1`, `l = -1`; if it
  has merged a general form by then, this item is not added again.
- `eval_affineChart_dehomogenize_eq_twistTransition_mul`,
  `HasMFDerivAt.eval_affineChart_dehomogenize` and
  `contMDiffOn_eval_affineChart`: on `U_i ∩ U_j` the dehomogenizations of
  a homogeneous polynomial of degree `d`, read in the charts, differ by
  `twistTransition d i j`, and so do their differentials at a zero; a
  polynomial read in the chart at `i` is `C^r` on `U_i`. They are used by
  `Hypersurface/NormalBundle.lean`, which imports this file.

### `Geometry/Manifold/Projectivization/EulerSequence.lean`

Namespace `Projectivization`, on `ℙ ℂ (Fin (m + 1) → ℂ)`.

- `eulerSequenceEquiv m x : (TangentSpace 𝓘(ℂ, Fin m → ℂ) ×ᵇ
  Bundle.Trivial _ ℂ) x ≃L[ℂ] (twistPiCore 1 (Fin (m + 1))).Fiber x`, the
  splitting of the Euler sequence
  $0\to\mathbb C\to\operatorname{Hom}(\ell,\mathbb C^{m+1})\to T\mathbb
  CP^m\to0$ by the standard Hermitian product: in chart `i`, at the point
  $v$ with $v_i=1$, $(\xi,c)\mapsto P_{v^\perp}\tilde\xi+c\,v$, where
  $\tilde\xi$ is $\xi$ with a zero inserted at `i` and $P_{v^\perp}$ the
  orthogonal projection onto $v^\perp$. The fibre `ℂ^{m+1}` of
  `twistPiCore 1` in chart `i` is $\operatorname{Hom}(\ell,\mathbb C^{m+1})$
  evaluated at $v$, which is why its transitions are those of `twistCore 1`.
  With `eulerSequenceEquiv_apply` and the continuity of its map of total
  spaces and of its inverse, checked in the charts of both bundles (the
  tangent charts are the affine charts that `twistCore` also uses,
  `chartAt_eq_affineOpenPartialHomeomorph_twistCore_indexAt`).
- It uses the derivatives of the transition maps from
  `Geometry/Manifold/Instances/Projectivization.lean`, the Hermitian
  projector in the charts from
  `LinearAlgebra/Projectivization/HermitianProjector.lean`, and
  `normalizedRep` from `LinearAlgebra/Projectivization/Basic.lean`.

### `Geometry/Manifold/Projectivization/ChernClass.lean`

Namespace `Projectivization`, with `h := hyperplaneClass (Fin (m + 1) → ℂ)`.

- `chernClass_one_twistCore (k : ℤ)`: $c_1(\mathcal O(k))=k\,h$, by induction
  with `twistCoreTensorEquiv`, `TauCeti.complexEulerClass_tensorProduct`
  and `complexEulerClass_twistCore_one` (#1040), read through
  `chernClass_one_eq_complexEulerClass`; `totalChernClass_twistCore`:
  $c(\mathcal O(k))=1+k\,h$.
- `totalChernClass_twistPiCore (k : ℤ) (r : ℕ)`: $c(\mathcal O(k)^{\oplus
  r})=(1+k\,h)^r$, for `ι = Fin r`, by induction with
  `twistPiCoreOptionEquiv`, `totalChernClass_prod` and `totalChernClass_congr`.
- **Milestone, part 1** `totalChernClass_tangentSpace`:
  `totalChernClass _ (TangentSpace 𝓘(ℂ, Fin m → ℂ)) = (1 + h) ^ (m + 1)` in
  `EvenIntegralCohomology`, from `eulerSequenceEquiv`, `totalChernClass_prod`
  and `totalChernClass_trivial`. For the page's $\mathbb CP^{n+1}$, `m = n + 1`.
  The isomorphism of part 1 is `eulerSequenceEquiv`. Its docstring ends with
  the line Milestone: *Chern classes of projective hypersurfaces*.

### `Geometry/Manifold/SmoothEmbedding/NormalSpace/Splitting.lean`

Namespace `TauCeti.SmoothEmbedding`, for `f : SmoothEmbedding I J n M N`
with `hn : n ≠ 0`, between finite-dimensional manifolds over `𝕜`.

- `tangentNormalEquiv f hn r hr x : (TangentSpace I ×ᵇ fun x ↦ f.isImmersion.NormalSpace x hn) x
  ≃L[𝕜] (f *ᵖ TangentSpace J) x`, `(u, a) ↦ df u + r a`, for any fibrewise
  linear right inverse `r` of `normalClass` (`hr`), with
  `tangentNormalEquiv_apply` and the continuity of its map of total spaces
  and of its inverse (with the normal bundle of model `P`, `hdim`) when that
  of `r` is continuous. Bijective since the image of `df` is the kernel of
  `normalClass` (Tau Ceti's `NormalSpace` is that quotient). *Adjunction*'s
  `normalSplitting` is its inverse for the representatives in the
  `ω`-orthogonal.
- `normalRightInverse f hn x : f.isImmersion.NormalSpace x hn →L[𝕜] TangentSpace J (f x)`,
  with `[IsRCLikeNormedField 𝕜]` and `[NormalSpace M] [ParacompactSpace M]` (for
  a partition of unity), with `normalClass_normalRightInverse` (a right inverse
  of `normalClass`) and the continuity of its map of total spaces; the right
  inverse that Tau Ceti's `Continuous.exists_continuous_clm_bundle_rightInverse`
  gives to `normalClass`, a continuous section of the Hom bundle from
  `f *ᵖ TangentSpace J` to the normal bundle.

### `Geometry/Manifold/Projectivization/Hypersurface/NormalBundle.lean`

Namespace `SymplecticGeometry.SmoothProjectiveHypersurface`.

- `normalSpaceEquiv X x : X.embedding.isImmersion.NormalSpace x _ ≃L[ℂ]
  (twistCore d).Fiber (x : ℙ ℂ (Fin (n + 2) → ℂ))`, in the chart
  `(twistCore d).indexAt x`, Tau Ceti's
  `complexProjectiveZeroLocusNormalSpaceEquiv`; with
  `normalSpaceEquiv_normalClass` (the differential of the dehomogenized
  polynomial), the chart change lemma above, and the continuity of its map
  of total spaces and of its inverse, from the pull-back bundle
  `X.embedding *ᵖ (twistCore d).Fiber` (Tau Ceti's
  `contMDiff_normalBundle_iff` or its continuous form, through the quotient
  map from the pulled-back tangent bundle).

### `Geometry/Manifold/Projectivization/Hypersurface/ChernClass.lean`

- `X.hyperplaneClass : (TopCat.of X).integralCohomology 2`, the pull-back of
  `hyperplaneClass` by the inclusion, with `hyperplaneClass_def`; and its
  image in `EvenIntegralCohomology`.
- **Milestone, part 2 (first half)** `chernClass_one_normalSpace`:
  `chernClass ℂ (X.embedding.isImmersion.NormalSpace · _) 1 = d • X.hyperplaneClass`, from
  `normalSpaceEquiv`, `chernClass_congr`, `chernClass_pullback` and
  `chernClass_one_twistCore`.
- **Milestone, part 3** `totalChernClass_tangentSpace_mul`:
  `totalChernClass _ (TangentSpace _) * (1 + d • ι^*h) = (1 + ι^*h) ^ (n + 2)`
  in `EvenIntegralCohomology (TopCat.of X)`, from `tangentNormalEquiv`,
  `totalChernClass_prod`, `totalChernClass_pullback` and
  `totalChernClass_tangentSpace`; and its consequences
  `chernClass_tangentSpace` (for each `k`, $c_k(TX)$ is
  $\sum_{j\le k}\binom{n+2}{k-j}(-d)^j$ times $(\iota^*h)^k$, since
  $1+d\,\iota^*h$ is invertible with inverse $\sum_j(-d\,\iota^*h)^j$) and
  `chernClass_one_tangentSpace` ($c_1(TX)=(n+2-d)\,\iota^*h$, the
  coefficient in `ℤ`). Each docstring of a milestone part ends with the line
  Milestone: *Chern classes of projective hypersurfaces*.

### `Geometry/Manifold/Complex/EulerCharacteristic.lean`

For a compact Hausdorff complex manifold `M` modelled on `𝓘(ℂ, E)` with
`finrank ℂ E = r + 1`, `M : Type`.

- No new homeomorphism of tangent bundles: Tau Ceti's
  `(TangentBundle.restrictScalarsHomeomorph ℝ M).symm`
  (`Geometry/Manifold/VectorBundle/Tangent/RestrictScalars.lean`) is the
  identity of total spaces from the real tangent bundle to the complex one,
  linear on fibres by its `_apply` and `_symm_apply` lemmas. With it, Tau
  Ceti's `TauCeti.complexEulerClass_tangentSpace_eq_eulerClass`
  (`Geometry/Manifold/Complex/EulerClass.lean`) identifies the complex Euler
  class of the tangent bundle with the Euler class of the real one, oriented
  by `complexManifoldOrientation E M`.
- `SymplecticGeometry.evalFundamentalClass_chernClass_eq_eulerChar`:
  $\langle c_{r+1}(TM),[M]\rangle=\chi(M)$, from
  `chernClass_finrank_eq_complexEulerClass` (#1043), the previous item, and
  `evalFundamentalClass_eulerClass_eq_eulerChar_of_finiteCWType` (#1045). The evaluation
  must commute with `uliftIntegralCohomologyIso`, as the review of #896
  noted; if #1029 does not prove it, this issue does.

### `Geometry/Manifold/Projectivization/Hypersurface/Line.lean`

- `card_inter_line`: if `ι : ℂ² → ℂⁿ⁺²` is linear and injective and the line
  it spans is transverse to `X` at every common point, it meets `X` in
  exactly `d` points. The binary form `poly ∘ ι` argument above, with the
  count of zeros of a binary form in `LinearAlgebra/Projectivization/BinaryForm.lean`.
- `card_eq` (**milestone, part 2 for `n = 0`**, finitely many points
  of $\mathbb CP^1$): `Nat.card X = d`, the line being all of $\mathbb CP^1$.
  For `n = 0` the pairing with $[X]$ is read as this count of points, since
  Tau Ceti's fundamental classes need positive dimension. Its docstring ends
  with the milestone line.
- `eulerChar_eq_of_dim_zero` (**milestone, part 4 for `n = 0`**):
  `TauCeti.eulerChar X = d`, with the instance
  `TauCeti.FiniteCWType.of_discreteTopology` on `X`, from `card_eq` and
  Tau Ceti's `TauCeti.eulerChar_of_discreteTopology`. Its docstring ends
  with the milestone line.

### `Geometry/Manifold/Projectivization/Hypersurface/Degree.lean`

For `n ≠ 0`.

- `complexEulerClass_twistPiCore_pullback`: the Euler class of
  $\iota^*\mathcal O(1)^{\oplus n}$ is $(\iota^*h)^n$, from
  `totalChernClass_twistPiCore`, `totalChernClass_pullback` and
  `chernClass_finrank_eq_complexEulerClass`.
- `sectionIndex_eq_one_of_complexLinear` (in
  `Topology/VectorBundle/Orientation/SectionIndex/ComplexLinear.lean`, in the namespace
  `SymplecticGeometry`, for any complex bundle over a complex
  manifold oriented by `complexManifoldOrientation`): at a zero where a
  section has a complex-linear invertible derivative in a holomorphic chart
  and a complex trivialization, its index for the complex orientation is
  $1$.
- **Milestone, part 2 (second half)** `evalFundamentalClass_hyperplaneClass_pow`:
  $\langle(\iota^*h)^n,[X]\rangle=d$, by the argument of *Decisions*.

### `Geometry/Manifold/Projectivization/Hypersurface/EulerCharacteristic.lean`

For `n ≠ 0`.

- **Milestone, part 4** `eulerChar_eq_evalFundamentalClass_chernClass`:
  $\chi(X)=\langle c_n(TX),[X]\rangle$, the general theorem of issue 7 for `X`.
- `eulerChar_eq`: $\chi(X)=d\sum_{j\le n}\binom{n+2}{n-j}(-d)^j$, from
  `chernClass_tangentSpace` and `evalFundamentalClass_hyperplaneClass_pow`,
  and for every `n`: for `n = 0` it is `eulerChar_eq_of_dim_zero`.

### `Geometry/Manifold/Projectivization/Hypersurface/Veronese.lean`

For `d ≠ 0`, as an instance `[NeZero d]` where it is needed; all of it is the
setting of Tau Ceti's Lefschetz theorems.

- `X.veroneseEquiv`, the linear equivalence of the space of monomials with
  `Fin (veroneseDim (n + 2) d - 1 + 1) → ℂ` (the form Tau Ceti's atlas on
  projective space takes) sending the form to coordinate `0`, and
  `X.veroneseImage`, the closed set $Y$, with
  `veroneseImage_inter_hyperplane`: $Y\cap\{x_0=0\}$ is the image of `X`.
- `X.veroneseHomeomorph : ℙ ℂ (Fin (n + 2) → ℂ) ≃ₜ X.veroneseImage`.
- The affine part: `X.veroneseAffine`, the set $Z$, with its
  `ChartedSpace (Fin (n + 1) → ℂ)` and `IsManifold 𝓘(ℂ, _) r` structure, for every `r`,
  carried from the open set of $\mathbb CP^{n+1}$ outside `X`;
  `contMDiff_coe_veroneseAffine` and `injective_mfderiv_coe_veroneseAffine`,
  the hypotheses `hZval` and `hinj` of Tau Ceti's theorems.
- `exists_homotopyEquiv_nhds`: a neighbourhood $W$ of $Y\cap\{x_0=0\}$ in $Y$
  whose inclusion is a homotopy equivalence, from
  `exists_homotopyEquiv_subset` as above.
- General steps in files of their own: `LinearEquiv.exists_apply_eq_sum_mul`
  (`LinearAlgebra/Pi/LinearForm.lean`) and
  `MvPolynomial.IsHomogeneous.veroneseLinearForm_coeff_ne_zero`
  (`LinearAlgebra/Projectivization/VeroneseLinearForm.lean`) for `veroneseEquiv`;
  `TauCeti.SmoothEmbedding.restrictScalars`
  (`Geometry/Manifold/SmoothEmbedding/RestrictScalars.lean`) for the tubular
  neighbourhood.

### `Geometry/Manifold/Projectivization/Hypersurface/Lefschetz.lean`

For `d ≠ 0`, with the inclusion `X → ℙ ℂ (Fin (n + 2) → ℂ)`.

- `isIso_homologyMap_subtypeVal`: for `k < n` and coefficients `R`
  in an abelian category with coproducts, the inclusion induces an
  isomorphism on $H_k$; `bijective_homotopyGroupMap_subtypeVal`: the same
  for $\pi_k$ at any base point. From Tau Ceti's `isIso_homologyMap_notMem_affineOpen`
  and `bijective_homotopyGroupMap_notMem_affineOpen`, transported along
  `veroneseHomeomorph`.
- `connectedSpace` (for `n ≠ 0`), from `joined_notMem_affineOpen_iff` and
  `X.nonempty`; `simplyConnectedSpace` (for `2 ≤ n`).
- General steps in files of their own:
  `ContinuousMap.isIso_homologyMap_iff_of_comp_eq`
  (`AlgebraicTopology/Singular/HomologyMap.lean`),
  `ContinuousMap.IsNConnected.pathConnectedSpace_iff`
  (`Topology/Homotopy/HomotopyGroup/ConnectedMap/PathConnected.lean`), and the
  instance `Projectivization.instSimplyConnectedSpaceComplex`
  (`Topology/ComplexProjectiveSpace/SimplyConnected.lean`).

### `AlgebraicTopology/Cohomology/Cap/RationalCoefficients.lean` (addition)

In the namespace `TauCeti.HomologicalOrientation`:

- `bijective_singularCapLinearMap_fundamentalClass`: for a compact
  homologically oriented `m`-manifold and `p + q = m`, capping with the image
  of the fundamental class is a bijection `Hᵖ(M; ℚ) → H_q(M; ℚ)`, with no
  hypothesis on the duality map, by #810's bijectivity of the duality map;
- `bettiNumber_eq_bettiNumber`: for a compact homologically oriented
  `m`-manifold and `p + q = m`, `bettiNumber ℚ M q = bettiNumber ℚ M p`, from
  #810's bijectivity of the duality map and Tau Ceti's
  `TopCat.finrank_singularHomology_eq_of_bijective_singularCapLinearMap`.

### `Geometry/Manifold/Projectivization/Hypersurface/BettiNumber.lean`

For `d ≠ 0`.

- `bettiNumber_of_ne`: for `k ≠ n`, `bettiNumber ℚ X k` is `1` if `k` is even
  and `k ≤ 2 * n`, and `0` otherwise; below `n` by
  `isIso_homologyMap_subtypeVal` and the homology of $\mathbb CP^{n+1}$,
  above by `bettiNumber_eq_bettiNumber`, and above `2 * n` by Tau Ceti's
  vanishing of homology above the dimension of a manifold.
- `bettiNumber_middle`: $(-1)^n b_n=\chi(X)-(n+1)+[n\text{ even}]$, from
  the alternating sum of #1045 (`evalFundamentalClass_eulerClass_eq_sum_finrank_singularHomology`)
  and `eulerChar_eq`.

### `Geometry/Manifold/Projectivization/Hypersurface/Surface.lean`

For `X : SmoothProjectiveHypersurface 2 d`, with `d ≠ 0` for $b_2$ and
$b^\pm$. Each theorem's
docstring ends with the line Milestone: *Chern classes of projective
hypersurfaces*.

- `chernClass_one_tangentSpace_surface` and `chernClass_two_tangentSpace_surface`:
  $c_1=(4-d)\,\iota^*h$, $c_2=(d^2-4d+6)\,(\iota^*h)^2$;
  `eulerChar_surface`: $\chi=d^3-4d^2+6d$.
- `bettiNumber_two_surface`: $b_2=d^3-4d^2+6d-2$, from `bettiNumber_middle`.
- `signature_surface`: with `σ` the signature above and `q` the quadratic
  form of the intersection form, and the hypothesis
  `3 * σ = ⟨c₁ ⌣ c₁, [X]⟩ - 2 * ⟨c₂, [X]⟩`, the three equations
  $3\sigma=(4-d^2)d$, $3b^+=d^3-6d^2+11d-3$ and $3b^-=2d^3-6d^2+7d-3$ in
  `ℤ`, the page's formulas with the denominators cleared.

### `Geometry/Manifold/Projectivization/Hypersurface/Threefold.lean`

For `X : SmoothProjectiveHypersurface 3 d`, with `d ≠ 0` for the Betti
numbers, with the milestone
line: `chernClass_one_tangentSpace_threefold` ($c_1=(5-d)\,\iota^*h$),
`bettiNumber_two_threefold`, `bettiNumber_four_threefold` ($b_2=b_4=1$) and
`bettiNumber_three_threefold` ($b_3=d^4-5d^3+10d^2-10d+4$).

### `Geometry/Manifold/Projectivization/Hypersurface/PlaneCurve.lean`

For `X : SmoothProjectiveHypersurface 1 d` with `d ≠ 0`:

- `two_mul_surfaceGenus`: `2 * (TauCeti.surfaceGenus X : ℤ) = (d - 1) * (d - 2)`,
  the example of *Adjunction formula*, with the line Milestone: *Adjunction
  formula*. From $\chi(X)=d(3-d)$ (`eulerChar_eq`), which is even and at most
  $2$, Tau Ceti's `RiemannSurface.eulerChar_eq_two_sub_two_mul_genus_iff`
  and `HomologicalOrientation.genus_eq_surfaceGenus`, the curve being
  connected (`connectedSpace`). No evenness of $b_1$ and no self-intersection
  number is needed.

## What the part uses

- *Chern classes* (#881): `chernClass`, `totalChernClass`,
  `EvenIntegralCohomology`, `evenIntegralCohomologyMap`, `hyperplaneClass`
  (#1028, #1034, #1035); `chernClass_pullback`, `chernClass_congr`,
  `chernClass_trivial` (#1037); `totalChernClass_prod` (#1038);
  `complexEulerClass_tensorProduct`, `complexEulerClass_twistCore_one`
  (#1040); `chernClass_finrank_eq_complexEulerClass` (#1043);
  `evalFundamentalClass_eulerClass_eq_eulerChar_of_finiteCWType` and the alternating sum
  (#1045).
- *First Chern number*'s prerequisites: Poincaré duality (#810), and the
  library's merged `Cap/RationalCoefficients.lean`.
- *Complex projective space*: `ContMDiff.restrictScalars'`
  (`Geometry/Manifold/ContMDiff/RestrictScalars.lean`), which
  `SmoothEmbedding/RestrictScalars.lean` imports.
- Tau Ceti: projective space and its zero loci
  (`Geometry/Manifold/Projectivization/ZeroLocus.lean`), the line bundles
  `twistCore` and `homogeneousSection`, the Veronese map, the Lefschetz
  theorems, normal bundles of embeddings (`Geometry/Manifold/SmoothEmbedding/NormalSpace/`),
  tubular neighbourhoods (`Geometry/Manifold/TubularNeighborhood/Existence.lean`),
  generic sections, section indices, Euler classes and their complex
  orientations, the orientation of complex manifolds, tensor products of
  bundles, the homology and simple connectivity of $\mathbb CP^n$, Betti
  numbers, the cup pairing, signatures of quadratic forms, the genus of
  surfaces.
- Mathlib: `MvPolynomial`, `Polynomial` roots over `ℂ`,
  `SmoothPartitionOfUnity`, `sigPos`, `sigNeg`.

Mathlib, Tau Ceti and this library were searched, at the pinned versions,
for the Euler sequence, Chern classes of $\mathcal O(k)$, the normal bundle of
a hypersurface as a bundle, a splitting of the tangent bundle along an
embedding, the degree of a hypersurface, the Lefschetz neighbourhood
hypothesis, and an intersection form of a four-manifold. Tau Ceti has the
pointwise normal space of a zero locus, the conditional Lefschetz theorems,
tubular neighbourhoods, and the cup pairing, as cited; none of the rest.

## Building issues

In this order. Each issue is blocked by the ones listed, and all are
sub-issues of #883, *Build the part Projective hypersurfaces*. Sizes are
estimates. Issues 1, 2 and 4 can start once this design is merged, and
issues 3, 5, 9 and 12 once their blockers in this list are; none of these
waits for another part.

| # | Issue | Files | Blocked by | Size |
|---|---|---|---|---|
| 1 | Smooth projective hypersurfaces | `Hypersurface/Basic.lean` | — | 250 |
| 2 | Sums and tensor products of the bundles $\mathcal O(k)$ | `Projectivization/TwistCore.lean` | — | 300 |
| 3 | The Euler sequence | `Projectivization/EulerSequence.lean` | 2 | 400 |
| 4 | Splitting the tangent bundle along an embedding | `NormalSpace/Splitting.lean` | — | 300 |
| 5 | The normal bundle of a hypersurface | `Hypersurface/NormalBundle.lean` | 1, 2 | 350 |
| 6 | Chern classes on projective space (part 1) | `Projectivization/ChernClass.lean` | 2, 3; #1037, #1038, #1040, #1043 | 250 |
| 7 | The Euler characteristic of a compact complex manifold | `Complex/EulerCharacteristic.lean` | #1043, #1045 | 250 |
| 8 | Chern classes of a hypersurface (parts 2 and 3) | `Hypersurface/ChernClass.lean` | 4, 5, 6 | 250 |
| 9 | Transverse lines meet a hypersurface in $d$ points; the case `n = 0` of parts 2 and 4 | `Hypersurface/Line.lean` | 1 | 300 |
| 10 | The degree $\langle\iota^*h^n,[X]\rangle=d$ | `Hypersurface/Degree.lean` | 6, 8, 9 | 400 |
| 11 | The Euler characteristic of a hypersurface (part 4) | `Hypersurface/EulerCharacteristic.lean` | 7, 8, 10 | 150 |
| 12 | The Lefschetz theorems for hypersurfaces | `Hypersurface/Veronese.lean`, `Hypersurface/Lefschetz.lean` | 1 | 500 |
| 13 | Poincaré duality for rational Betti numbers | `Cap/RationalCoefficients.lean` | #810 | 100 |
| 14 | Betti numbers of hypersurfaces | `Hypersurface/BettiNumber.lean` | 11, 12, 13 | 250 |
| 15 | Surfaces, threefolds and plane curves | `Hypersurface/Surface.lean`, `Threefold.lean`, `PlaneCurve.lean`; the `ERRATA.md` entry for `d = 0` | 11, 12, 14 | 350 |

Issue 12 may be split in two at the file boundary if it grows past a few
hundred lines; issue 15 likewise, with the plane curves (blocked by 11 and
12 only) first. The milestone's parts are proved in issues 6, 8, 9, 10 and
11, its numerical consequences in 15, and the example of *Adjunction formula*
in 15.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §4.4, Examples 4.4.3–4.4.5, Exercise 4.4.6.
* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §2, and Chapter 1, §1.
* [A. Andreotti, T. Frankel, *The Lefschetz theorem on hyperplane sections*][AndreottiFrankel1959].
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton
  (1963), §7.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in
  Mathematics 218, Springer (2013), Theorem 6.24.
* A. Hatcher, *Algebraic Topology*, Cambridge (2002), §3.3.
