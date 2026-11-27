# Symplectic sums

This is the detailed design of part 62 of `DESIGN.md`, *Symplectic sums*.
It proves the four milestones of §7.2 of
`atlas/constructing-symplectic-manifolds.md`: *Pointwise connected-sum
obstruction for symplectic forms*, *Symplectic fibre connected sum with
trivial normal bundles*, *Fundamental group after summing with the rational
elliptic surface* and *Gompf's realization of finitely presented groups*.
They follow McDuff–Salamon [McDuffSalamon2017], §7.2 (Lemma 7.2.2, the
fibre sum on pp. 318–319, Exercise 7.2.6, Theorem 7.2.8), and Gompf
[Gompf1995] for the fibre sum and the realization theorem.

All names below are in the namespace `SymplecticGeometry` unless they are
written with another one. Paths of new files are under `SymplecticGeometry/`;
Tau Ceti paths are relative to `.lake/packages/TauCeti/TauCeti/`. Merged
declarations named below were checked against the library and Tau Ceti
`0651fdbae946`. Names given for other parts that are not yet built are those
of `DESIGN.md`; the issue that uses one checks it against that part's
design file once it exists.

## Setting and notation

- **Manifolds and forms.** Symplectic manifolds are, as in the rest of the
  library, Hausdorff, second countable manifolds without boundary over a
  model `I`, with a `SmoothTwoForm I M` that is `IsSymplectic` (Tau Ceti).
  Restriction to an open set `U` is the pull-back along `Subtype.val`, as in
  the merged symplectic neighbourhood theorem
  `HasSymplecticTangentImages.exists_symplectomorphism_opens`
  (`Geometry/Symplectic/Neighborhood/Symplectic.lean`).
- **The disc and its form.** $B^2(\varepsilon)$ is `Metric.ball (0 : ℂ) ε`
  over `𝓘(ℝ, ℂ)`, with $\omega_0=dx\wedge dy$, the constant form of Tau Ceti's
  `stdComplexSymplecticForm` on `ℂ`. The annulus
  $A(\delta,\varepsilon)=\{\delta<|z|<\varepsilon\}$ is an open subset of
  `ℂ`.
- **Product model.** For a symplectic manifold $(Q,\tau)$ the product
  $Q\times B^2(\varepsilon)$ carries $\tau\oplus\omega_0$, Tau Ceti's
  `TauCeti.SmoothTwoForm.IsSymplectic.prod`.
- **Homotopy through nondegenerate forms.** As in the merged
  `firstChernClass_mpullback_prodMk_eq`, a homotopy from $\sigma_0$ to
  $\sigma_1$ on $U$ is a smooth two-form on `ℝ × U` whose slices
  `mpullback (Prod.mk t)` are nondegenerate for $t\in[0,1]$ and equal
  $\sigma_0$, $\sigma_1$ at $t=0,1$. No new predicate is introduced: the
  milestone writes these conditions out.
- **Framings.** A symplectic framing of the normal bundle of a symplectic
  embedding $\iota:Q\to M$, `SymplecticFraming` in
  `Geometry/Symplectic/Sum/ProductNeighborhood.lean`, is a family of
  continuous linear isomorphisms from the normal spaces of
  $q\mapsto(q,0)$ in $Q\times\mathbb C$ (`zeroSlice`) to `ι.isImmersion.NormalSpace q`
  that is smooth as a map of total spaces and carries the
  `TauCeti.SmoothEmbedding.symplecticNormalForm` of `zeroSlice` (that is,
  $\omega_0$) to that of $\iota$. These are the hypotheses
  `Φ`, `hΦ`, `hΦσ` of the merged neighbourhood theorem.

## Decisions

These settle the points that part 62 of `DESIGN.md` leaves to this file,
and the note of the review of #3195.

1. **Gluing two manifolds.** The fibre sum glues two manifolds along open
   subsets by a diffeomorphism. Tau Ceti does not have this gluing in general
   (its `TauCeti.ConnectedSum` glues only along punctured balls). The new file
   `Geometry/Manifold/Gluing/Pair.lean` builds it once, as a two-piece
   `TopCat.GlueData` with Tau Ceti's `Geometry/Manifold/Gluing/GlueData.lean`,
   with Hausdorffness from `TopCat.GlueData.t2Space_iff_isClosed_chartRel`
   (the graph of the gluing map is closed) and forms glued pointwise: at
   `inl x` the glued form is $\sigma_1$ at $x$ read through the inverse of
   the differential of `inl` (`TauCeti.RoughForm.pushforwardAt`), and at
   the other points likewise through `inr`. Its pull-back by `inr` is
   $\sigma_2$ on $U_2$ exactly because
   $\varphi^*(\sigma_2|_{U_2})=\sigma_1|_{U_1}$, a pointwise condition.
   `IsLocalDiffeomorph.exists_mpullback_eq_iff` does not apply: it asks for
   self-maps of all of $M_1\sqcup M_2$ relating the points of each fibre,
   and swapping $u$ with $\varphi(u)$ is not continuous at the boundary of
   $U_1$. Smoothness of the glued form is local, since `inl` and `inr`
   are local diffeomorphisms. Part 57's
   `ConnectedSum/Annulus.lean` (#3275) may use it too; this file does not
   wait for it.
2. **The fibre sum is glued along open collars, not cut at the seam.** The
   pieces are $M_i\setminus f_i(Q\times\bar B(\delta))$, open since $Q$ is
   compact, glued along $f_1(Q\times A(\delta,\varepsilon))$ and
   $f_2(Q\times A(\delta,\varepsilon))$ by $f_2\circ(\mathrm{id}_Q\times a)\circ f_1^{-1}$,
   where $a$ is the annulus map of `Collar.lean`. The page's note offers
   cutting at the fixed radius $\sqrt{(\delta^2+\varepsilon^2)/2}$ and gluing
   boundaries; open gluing needs no boundary charts, and the closed graph
   follows from compactness of $Q$: a sequence of the overlap whose radius
   tends to $\varepsilon$ on one side has radius tending to $\delta$ on the
   other, so it has no limit in the other piece. The framings, $\varepsilon$,
   $\delta$ and the product neighbourhoods are data of the construction, as
   the page asks.
3. **Product neighbourhoods.** They come from the merged neighbourhood
   theorem applied to $q\mapsto(q,0)$ in $Q\times\mathbb C$ and to
   $\iota_i$, with the framing as `Φ`; compactness of $Q$ and the tube lemma
   give $\varepsilon$ with $Q\times B^2(\varepsilon)$ inside the open set
   that theorem gives.
4. **The pencil.** $E(1)$ is the total space of the Hesse pencil, the
   hypersurface
   $\{([x:y:z],[s:t]) : s(x^3+y^3+z^3)+t\,xyz=0\}$ of
   $\mathbb CP^2\times\mathbb CP^1$. It is smooth: away from the nine base
   points $\{x^3+y^3+z^3=xyz=0\}$ the derivative in the $\mathbb CP^1$
   direction is nonzero, and at the base points the two cubics meet
   transversally, so $s\nabla f+t\nabla g\ne0$. The torus is the fibre over
   $[1:0]$, the Fermat cubic, which the library already has as
   `SmoothProjectiveHypersurface.fermat 1 3`
   (`Geometry/Manifold/Projectivization/Hypersurface/Basic.lean`).
5. **Symplectic, not Kähler.** $E(1)$ needs a symplectic form, not a Kähler
   one. The product $\omega_{\mathrm{FS}}\oplus\omega_{\mathrm{FS}}$ tames the
   product complex structure, so by *Complex submanifolds*
   (`Geometry/Symplectic/Manifold/AlmostComplex/Submanifold.lean`) its
   pull-back to $E(1)$ is nondegenerate, and it is closed. No product of
   Kähler structures is needed.
6. **Simple connectivity without the blowup.** $\pi_1(E(1))=1$ is proved by
   van Kampen for the cover of $E(1)$ by the preimage of $\mathbb CP^2$
   minus the nine base points, which the projection maps homeomorphically
   onto a simply connected set (Tau Ceti's
   `TauCeti.fundamentalGroup_map_subtypeVal_compl_singleton_bijective`, real
   dimension four), and nine neighbourhoods of the exceptional curves
   $\{p\}\times\mathbb CP^1$. In local coordinates $u=f/h$, $v=g/h$ at a base
   point each neighbourhood is $\{(u,v,[s:t]) : su+tv=0, |u|^2+|v|^2<r^2\}$,
   which the scaling $(u,v)\mapsto\lambda(u,v)$ retracts onto
   $\mathbb CP^1$, a simply connected sphere. This replaces the route of
   `DESIGN.md` through *Complex blowup*'s `ConnectedSum.lean`; see
   *Departures*.
7. **The fibre complement.** $\pi_1(E(1)\setminus T)=1$: van Kampen for
   $E(1)=(E(1)\setminus T)\cup N(T)$ shows that the meridian normally
   generates it, and the exceptional curve through a base point is a section
   of the pencil meeting $T$ once, so minus a small disc it is a disc in the
   complement bounding the meridian.
8. **The torus model.** The milestones on sums with $E(1)$ glue along
   embeddings of one fixed torus. That is Tau Ceti's standard symplectic
   torus `∀ i : Unit ⊕ Unit, AddCircle (p i)` with
   `TauCeti.torusSymplecticForm p` and `TauCeti.isSymplectic_torusSymplecticForm`
   (`Geometry/Symplectic/Manifold/Torus/Basic.lean`), of area
   $p_{\mathrm{inl}}\,p_{\mathrm{inr}}$, so that the tori of the realization
   theorem are parametrized directly; its fundamental group is
   `AddCircle.piFundamentalGroupMulEquivZero`. The fibre $T$ is
   identified with it by a diffeomorphism in three steps: the linear map
   $[x:y:z]\mapsto[-12z:36(x-y):x+y]$ of $\mathbb CP^2$ carries the Fermat
   cubic onto the Weierstrass cubic $Y^2Z=X^3-432Z^3$; Tau Ceti's
   `WeierstrassCurve.exists_continuousAddEquiv_periodLattice_contMDiff`
   (`Analysis/SpecialFunctions/Elliptic/Holomorphic.lean`) identifies that
   curve with $\mathbb C/\Lambda$ biholomorphically; and a real basis of
   $\Lambda$ identifies $\mathbb C/\Lambda$ with the standard torus. The
   first step compares the charts of `SmoothProjectiveHypersurface` with
   those of `WeierstrassCurve.Projective.Point.instIsManifold`, both complex
   submanifolds of $\mathbb CP^2$. The third step is a real-linear map of
   `ℂ` sending $\Lambda$ to $p_{\mathrm{inl}}\mathbb Z+ip_{\mathrm{inr}}\mathbb Z$,
   followed by Tau Ceti's covering map `TauCeti.complexPiTorusCover p`, which
   pulls `torusSymplecticForm p` back to $\omega_0$
   (`TauCeti.mpullback_complexPiTorusCover_torusSymplecticForm`). Areas are
   then matched by rescaling the form of $E(1)$ to the area of the periods,
   and the forms on the torus by Moser (*Moser isotopy*'s
   `TauCeti.SmoothTwoForm.exists_diffeotopy_mpullback_eq`), since two area
   forms of equal area on the torus are joined by a path of cohomologous
   area forms.
9. **The realization theorem without perturbing the form.** The page asks
   the design to fix how the perturbation $\rho\wedge\theta$ of Theorem 7.2.8
   is closed. The library keeps the product form, and so avoids that
   perturbation and Exercise 7.2.9; only the curves below are perturbed.
   For a smooth loop $\gamma_i$ in $F$, the torus
   $T_i=\{(\gamma_i(t),\,t+c_i,\,s)\}\subset F\times S^1_\beta\times S^1_\alpha$
   is embedded, since its $\beta$-coordinate is a degree-one graph, and it
   is symplectic for the product form $\omega_F+d\beta\wedge d\alpha$, which
   restricts to $dt\wedge ds$ on it. Its class in $\pi_1(F\times T^2)$ is
   $(\gamma_i,\beta)$, and the sum along a fibre $\{z\}\times T^2$ kills
   $\alpha$ and $\beta$, so the quotient is still
   $\pi_1(F)/\langle\!\langle\gamma_i\rangle\!\rangle$. Each curve
   $t\mapsto(\gamma_i(t),\beta_i(t))$, with $\beta_i$ increasing of degree
   one, is the graph over $S^1_\beta$ of a map $g_i:S^1\to F$, and
   $T_i$ is that graph times $S^1_\alpha$; the form restricts to
   $\beta_i'\,dt\wedge ds$ whatever $\gamma_i$ is. The $g_i$ start as the
   concatenations of the standard circles of $F$ through the base point, and
   are then moved by small homotopies so that $g_i(\beta)\ne g_j(\beta)$ for
   all $\beta$ and $i\ne j$: the map $\beta\mapsto(g_i(\beta),g_j(\beta))$
   from a circle into the four-manifold $F\times F$ generically misses the
   diagonal, of codimension two. This makes the $T_i$ pairwise disjoint, and
   the fibre point $z$ is taken off the images of the $g_i$. Only the free
   homotopy classes of the $\gamma_i$ enter the normal closure, so the
   homotopies do not change the quotient. Fixing the loops and choosing only
   the $\beta_i$ does not suffice: for the relators $a_1^2$ and $a_1^3$ the
   difference of the two $\beta$-coordinates on the set where the loops
   agree has nonzero degree, so it vanishes somewhere. Their normal
   bundles are pulled back from the oriented normal bundles of circles in
   the oriented three-manifold $F\times S^1_\beta$, so they are trivial, and a symplectic framing exists. The proof stays within the
   milestone: its statement is only the existence of $M$.
10. **The surface.** $F$ is the closed oriented surface of genus $g$, built
    as the iterated `TauCeti.ConnectedSum` of $g$ copies of the standard
    torus, with $\pi_1(F)$ identified with Tau Ceti's closed surface group
    `TauCeti.SurfaceGroup.Orientable g 0`
    (`GroupTheory/SurfaceGroup/Basic.lean`) by van Kampen. Neither library
    has this identification at the pinned commit; it is a prerequisite file
    of this part (issue 8). A presentation with $g$ generators and the
    relators, from `Group.IsFinitelyPresented.exists_mulEquiv_presentedGroup`,
    gives $G\cong\pi_1(F)/\langle\!\langle b_1,\dots,b_g,w_1,\dots,w_r\rangle\!\rangle$.
11. **Name.** `DESIGN.md`'s `Gompf.lean` is named after a person; the file
    is `FinitelyPresented.lean`, after what it proves.
12. **Dimension zero.** In the obstruction the Lean statement assumes
    $n\ne0$ as well as $2n\notin\{2,6\}$: for $n=0$ the summands are points,
    the sum is empty, and the empty form is symplectic with vacuous
    homotopies, so the claim fails. Unless the plan's conventions already
    exclude dimension zero, the issue that proves it records this in
    `ERRATA.md`, with that counterexample. That the summands are closed and
    connected, and that the balls respect the symplectic orientations, is
    not used by the proof (the argument only reads the forms near the two
    balls), so the statement drops these hypotheses, which makes it more
    general.

## Departures from `DESIGN.md`

`DESIGN.md` is corrected in the same pull request, in part 62, the table
of milestones and the convention *The rational elliptic surface*:
`Gompf.lean` becomes `FinitelyPresented.lean` (Decision 11);
`RationalEllipticSurface.lean` no longer uses *Complex blowup*'s
`ConnectedSum.lean` (Decision 6), so *Builds on* and the build-order row
drop *Complex blowup*; `Fibre.lean` glues along open collars rather than at
the fixed radius (Decision 2); `Pointwise.lean` works with nondegenerate
forms rather than tame structures (the two are equivalent by Tau Ceti's
`exists_compatible`); `E(1)` is shown symplectic rather than Kähler
(Decision 5); and the realization theorem does not perturb the product
form (Decision 9). The files this design adds outside
`Geometry/Symplectic/Sum/` are planned here only, and `DESIGN.md` does not
name them. The building issue #3287
is blocked only by #3286, so no blocker of an open issue changes.

## Files

### `Geometry/Manifold/Gluing/Pair.lean`

For spaces `M₁`, `M₂`, open sets `U₁`, `U₂` and a homeomorphism
`φ : U₁ ≃ₜ U₂`:

- `GluedAlong φ`, the glued space, with `GluedAlong.inl`, `GluedAlong.inr`,
  `isOpenEmbedding_inl`, `isOpenEmbedding_inr`, `range_inl_union_range_inr`
  and `inl_eq_inr_iff`, and the charted space instance when `M₁`, `M₂` are
  charted over one model.
- `GluedAlong.t2Space_of_isClosed_graph`: Hausdorff when both pieces are
  and the graph of `φ`, as a subset of `M₁ × M₂`, is closed.

For manifolds `M₁`, `M₂` over one model and a diffeomorphism
`φ : U₁ ≃ₘ^n⟮I, I⟯ U₂`, on `GluedAlong φ.toHomeomorph`:

- The `IsManifold` instance, from Tau Ceti's compatible
  gluing; `isLocalDiffeomorph_inl`, `isLocalDiffeomorph_inr`.
- `GluedAlong.gluedForm φ σ₁ σ₂ hσ`: forms `σ₁`, `σ₂` with
  `φ^*(σ₂|U₂) = σ₁|U₁` glue to the form whose pull-backs by `inl` and
  `inr` are `σ₁` and `σ₂` (`mpullback_inl_gluedForm`,
  `mpullback_inr_gluedForm`), the only one (`eq_gluedForm_iff`); it is
  closed, nondegenerate or symplectic exactly when both are
  (`isClosed_gluedForm_iff`, `isNondegenerate_gluedForm_iff`,
  `isSymplectic_gluedForm_iff`).

About 400 lines.

### `Geometry/Symplectic/Sum/Collar.lean`

- `annulusMap δ ε : ℂ → ℂ`,
  $z\mapsto\sqrt{\varepsilon^2+\delta^2-|z|^2}\,\bar z/|z|$, with
  `norm_annulusMap`, `annulusMap_annulusMap` (an involution of
  $A(\delta,\varepsilon)$), `mapsTo_annulusMap`, the fixed radius, and
  `annulusDiffeomorph δ ε hδ` (for `hδ : 0 ≤ δ`), a diffeomorphism of $A(\delta,\varepsilon)$.
- `mpullback_annulusMap`: it preserves $\omega_0$ (in polar coordinates it
  reverses both $r^2/2$ and $\theta$).
- `prodAnnulusDiffeomorph Q δ ε hδ`, the identity on `Q` times the annulus
  map, which preserves $\tau\oplus\omega_0$.

About 250 lines.

### `Geometry/Symplectic/Sum/Fibre.lean`

- `ProductNeighborhood Φ ε`, in `Sum/ProductNeighborhood.lean`: an open embedding $f$ of
  $Q\times B^2(\varepsilon)$ with $f(q,0)=\iota(q)$,
  $f^*\omega=\tau\oplus\omega_0$ and normal derivative given by `Φ`; with
  `ProductNeighborhood.exists` for small $\varepsilon$ and compact $Q$
  (Decision 3) and `isClosed_image_closedBall`.
- `FiberSum f₁ f₂ hδ hδε`, the `GluedAlong` of Decision 2, its `T2Space`, and
  `FiberSum.symplecticForm` with `isSymplectic_symplecticForm`,
  `mpullback_inl_symplecticForm` and `mpullback_inr_symplecticForm`.
- `exists_isSymplectic_fiberSum`: the milestone. For $(M_i,\omega_i)$ of
  dimension $2n$, compact $(Q,\tau)$ of dimension $2n-2$, symplectic
  embeddings $\iota_i$ with $\iota_i^*\omega_i=\tau$ and symplectic framings
  `Φᵢ`, there is $\varepsilon_0>0$ such that for $0<\varepsilon<\varepsilon_0$
  product neighbourhoods $f_i$ exist, and for every such $f_i$ and
  $0<\delta<\varepsilon$ the fibre sum is a Hausdorff, second countable
  manifold with a
  symplectic form restricting to $\omega_i$ on the two complements.
  Milestone: *Symplectic fibre connected sum with trivial normal bundles*.

About 500 lines.

### `Geometry/Symplectic/Sum/Pointwise.lean`

- `exists_isNondegenerate_of_connectedSum`: for open embeddings
  `e₁ : E → M₁`, `e₂ : E → M₂` of `E = EuclideanSpace ℝ (Fin (2 * n))` and
  radii $\rho_1,\rho_2>0$ with $\rho_1\rho_2<1$, a nondegenerate form on
  `TauCeti.ConnectedSum e₁ e₂` and homotopies through nondegenerate forms
  to $\omega_1$, $\omega_2$ on the summands with the closed balls removed,
  the images under `inl` and `inr` of $M_i\setminus e_i(\bar B(\rho_i))$
  (the book's punctured summands; the condition on the radii makes them
  cover the sum, as the book's do), give a nondegenerate form on the
  sphere of dimension $2n$. The sphere is the round one, with its two
  stereographic charts as a pair `TauCeti.IsComplementaryBall` (the
  inversion glues them as it glues the balls $e_1$, $e_2$ in the sum). In
  the chart of $e_i$ the form is $\omega_i$ within radius $\rho_i$, then the
  slice of the homotopy at a radial parameter, then the form of the sum
  near the equator. The slice part is the form
  $x\mapsto\sigma_{(\chi(x),x)}$ restricted to the $M$-directions, not the
  pull-back along $(\chi,\mathrm{id})$, which would add $d\chi$ terms.
- `not_exists_isSymplectic_connectedSum`: the milestone, for $n\ne0$ and
  $2n\notin\{2,6\}$ (Decision 12), by part 60's theorem that the sphere has
  no almost complex structure and Tau Ceti's
  `TauCeti.SmoothTwoForm.IsNondegenerate.exists_compatible`. Milestone:
  *Pointwise connected-sum obstruction for symplectic forms*.

About 450 lines.

### `Geometry/Manifold/Instances/Surface/Genus.lean`

Prerequisite of Decision 10: `ClosedSurface g`, the iterated connected sum
of `g` standard tori (the sphere for `g = 0`), a closed oriented surface,
with its coordinate balls `ClosedSurface.ball g j`, its base point and its
punctured torus summands. Its standard circles $a_k$, $b_k$ through the base
point and `ClosedSurface.fundamentalGroupMulEquiv` onto
`TauCeti.SurfaceGroup.Orientable g 0`, sending them to its generators, are
in the files of the next subsection, which import this one and
`Surface/PuncturedTorus.lean` (the punctured torus retracts onto the wedge
of two circles, and its fundamental group is `Orientable 1 1`).

#### The fundamental group of `ClosedSurface g`

Names were checked against the library and Tau Ceti `994bb2246b86`. Write
$c_j$ for the centre `ClosedSurface.ball g j 0` and
$X(g,n)$ for the complement of $c_0,\dots,c_{n-1}$.

- **Why punctures.** `ClosedSurface (g + 1)` is the sum of the torus with
  `ClosedSurface g` along the ball `0` of the latter, and its ball `j` is
  the ball `j + 1` of genus `g` (`ClosedSurface.succDiffeomorph_ball`). So
  van Kampen for $X(g+1,n)$ needs $X(g,n+1)$, and the induction on `g`
  runs over all `n` at once, against `Orientable g n`.
- **Statement.** `ClosedSurface.puncture g n :
  TopologicalSpace.Opens (ClosedSurface g)` is $X(g,n)$; it contains the
  base point. `ClosedSurface.exists_puncturedFundamentalGroupMulEquiv g n`
  says that there is an isomorphism
  `FundamentalGroup (puncture g n) ⟨basePoint g, _⟩ ≃* Orientable g n`
  sending the class of `circleLoop g k 0` to `a g n k`, that of
  `circleLoop g k 1` to `b g n k`, for `k : Fin g`, and that of
  `peripheralLoop g n i` to `peripheral g n i`, for `i : Fin n` (the loops
  are below). These elements generate `Orientable g n`, so the isomorphism
  is unique; `ClosedSurface.puncturedFundamentalGroupMulEquiv g n` is
  chosen from the theorem, with one `@[simp]` lemma for each of the three
  values, and `ClosedSurface.fundamentalGroupMulEquiv g` is its case
  `n = 0`, along `puncture g 0 = ⊤`, with the lemmas
  `fundamentalGroupMulEquiv_circleLoop_zero` and `_one` giving `a g 0 k`
  and `b g 0 k`.
- **Indices.** The peripheral index `i : Fin n` belongs to the ball
  `i.rev`, that is $c_{n-1-i}$. The ball `0`, along which the next torus
  is summed, is then always the last peripheral element, as
  `TauCeti.SurfaceGroup.Orientable.equivPushoutI` needs, and the indices
  agree from one genus to the next: the ball `i.rev` of genus `g + 1` and
  `n` punctures is the ball `(Fin.castSucc i).rev` of genus `g` and `n + 1`
  punctures.
- **Circles of the balls.** `ClosedSurface.ballCircle g j` is the loop
  `t ↦ ball g j (EuclideanTorus.neckIsometry (exp (2πit)))`, the circle of
  radius `1` of the ball, counterclockwise in its coordinates: the image of
  `LinearIsometryEquiv.circleLoop` for `neckIsometry` and `r = 1`. It
  starts at `ball g j (neckIsometry 1)`. Since the inversion in the unit
  sphere fixes that point, this circle of the ball `0` is the neck circle
  of the connected sum read in the second summand
  (`TauCeti.ConnectedSum.coe_map_neckInr_circleLoop_apply` with `r = 1`),
  and the neck point is the same on both sides
  (`TauCeti.ConnectedSum.inl_neckInl_eq_inr_neckInr`).
- **Connecting paths.** All paths below are paths in `ClosedSurface g`
  with a lemma that they meet no centre $c_j$, and are carried into each
  `puncture g n` by restricting their codomain.
  - `ClosedSurface.ballPath g j`, from the base point to the start of
    `ballCircle g j`: for `g + 1` the image under `inr` of
    `ballPath g (j + 1)`; for `g = 0` an explicit path in the sphere,
    below.
  - `ClosedSurface.summandPath g k`, from the base point to the point `0`
    of the torus summand `k`: for genus `g + 1` and `k = 0`, the image
    under `inr` of `ballPath g 0`, across the neck, then the image under
    `inl` of the reverse of `EuclideanTorus.peripheralPath`; for `k + 1`,
    the image under `inr` of `summandPath g k`.
- **Loops.** `ClosedSurface.circleLoop g k i` is `summandPath g k`, then
  the image of `EuclideanTorus.circleLoop i` under `summand k`, then
  `summandPath g k` back: these are the standard circles $a_k$ (`i = 0`)
  and $b_k$ (`i = 1`). `ClosedSurface.peripheralLoop g n i` is
  `ballPath g i.rev`, then `ballCircle g i.rev` **reversed**, then
  `ballPath g i.rev` back. The reversal is forced by the gluing: the neck
  generator goes to the last peripheral element `q₁` of the torus piece
  (`EuclideanTorus.puncturedFundamentalGroupMulEquiv_peripheralLoop`, the
  neck circle seen through `EuclideanTorus.peripheralPath`), and
  `TauCeti.SurfaceGroup.Orientable.gluingMaps` sends it to `q₂⁻¹` on the
  side of genus `g`, where it is the unreversed `ballCircle g 0` seen
  through `ballPath g 0`.
- **The step.** From the statement for `g` and `n + 1` to `g + 1` and `n`.
  Let `U` be the complement of $c_1,\dots,c_n$ in `ClosedSurface g`: open,
  connected, and containing the range of the ball `0`.
  `TauCeti.ConnectedSum.restrictRightHomeomorph` identifies
  `puncture (g + 1) n` with the connected sum of the torus with `U`, whose
  punctured second summand is `puncture g (n + 1)`. Then
  `TauCeti.ConnectedSum.isPushout_fundamentalGroup` at the neck point
  `circleBasepoint` of `neckIsometry` and `r = 1`, with the neck group `ℤ`
  generated by the circle
  (`LinearIsometryEquiv.fundamentalGroupComplSingletonMulEquivInt_circleLoop`).
  On the torus side, `EuclideanTorus.puncturedFundamentalGroupMulEquiv`
  moved to the neck point along `EuclideanTorus.peripheralPath` sends the
  generator to `peripheral 1 1 0`; on the other side, the isomorphism for
  `g` and `n + 1` moved along `ballPath g 0` sends it to
  `(peripheral g (n + 1) (Fin.last n))⁻¹`. These are
  `gluingMaps 1 0 g n`, so the square is identified with
  `Monoid.PushoutI (gluingMaps 1 0 g n)`, then by `equivPushoutI 1 0 g n`
  with `Orientable (1 + g) (0 + n)`, and by renaming the generators along
  `Fin.cast` with `Orientable (g + 1) n`. Since the torus piece has no
  other peripheral element, the product `P` of `equivPushoutI_a_natAdd` is
  empty and nothing is conjugated: the torus gives `a 0` and `b 0`, the
  generator `a k` of genus `g` gives `a k.succ`, as the summand `k` gives
  the summand `k.succ` (`ClosedSurface.succDiffeomorph_summand_succ`), and
  `peripheral (Fin.castSucc i)` gives `peripheral i`. Moving back to the
  base point along the image of `ballPath g 0` keeps the loops of genus
  `g` as they are and turns the torus loops into `circleLoop (g + 1) 0 i`,
  by the definition of `summandPath`. So the step is exact, and the
  statement holds for every `g` once it holds for `g = 0`.
- **The sphere needs explicit balls.** `ClosedSurfaceData.sphere` takes
  its balls from `exists_pairwise_disjoint_range_subset_compl_sphere` by
  choice, so nothing says whether they all induce the same orientation.
  If two of them induce opposite ones, then on the sphere minus their two
  centres, whose fundamental group is `ℤ`, their circles have the same
  class whatever the connecting paths, while `Orientable 0 2` needs `p`
  and `p⁻¹`; and two tori summed along such balls sit with opposite
  orientations, so that their circles do not satisfy the relation of
  `Orientable g 0`. So a refactor comes first: the balls of the sphere
  become `TauCeti.sphereBall v ∘ OpenPartialHomeomorph.univBall (j • e)
  (1 / 2)`, for the base point `v = (1, 0, 0)` and
  `e = EuclideanSpace.single 0 1` (the choice the existence proof already
  makes, with its vector fixed), with a lemma giving
  `ClosedSurface.ball 0 j` in this form.
- **The base case.** For `n = 0` the sphere is simply connected
  (`TauCeti.simplyConnectedSpace_sphere`) and `Orientable 0 0` is trivial.
  For `n ≥ 1` read the sphere in the chart `w ↦ -sphereBall v (-w)`
  complementary to `sphereBall v` (`TauCeti.isComplementaryBall_sphereBall`),
  which sends `0` to the base point and agrees with `sphereBall v` after
  the inversion in the unit circle. In it $c_0$ is the point at infinity
  and $c_j$, for `1 ≤ j`, is `j⁻¹ • e`, so $X(0,n)$ is the plane minus the
  points `1, 1/2, …, 1/(n - 1)` of the positive axis, based at `0`. The
  inversion reverses orientation, so after the reversal in
  `peripheralLoop` the loops about $c_j$, `j ≥ 1`, are small
  counterclockwise loops about these points, and the loop about $c_0$ is
  the circle of radius `2√2` about `0`, run clockwise from the angle
  `π / 4`. The paths `ballPath 0 j` are fixed for all `n`: for `j ≥ 1`
  from `0` down into the lower half-plane, along it to below `j⁻¹ • e`,
  and up to the circle; for `j = 0` the segment from `0` at the angle
  `π / 4` out to the large circle. Through
  `TauCeti.SurfaceGroup.Orientable.equivFreeGroup 0 (n - 1)` the statement
  becomes two facts about the plane minus a finite set `s` of positive
  reals, based at `0`: the counterclockwise loops about the points of `s`,
  reached from below the axis, are a free basis of the fundamental group;
  and a counterclockwise circle about `0` enclosing `s`, reached along a
  ray in the upper half-plane, is homotopic to these loops run one after
  the other, from the largest point of `s` to the smallest. In Mathlib's
  `FundamentalGroup` a product `x * y` runs `y` first, so the relation
  `p₀ ⋯ p_{n-1} = 1` says that the clockwise large circle followed by the
  loops about `1, 1/2, …, 1/(n - 1)` is trivial, which is the second fact.
  Tau Ceti proves both facts for two points
  (`TauCeti.ThricePuncturedSphere.fundamentalGroupMulEquivFreeGroup`, by
  `TauCeti.vanKampenEquiv` for two half-planes meeting in a strip, and
  `TauCeti.ThricePuncturedSphere.αPlus_trans_δ_trans_symm_homotopic_γ0_trans_γ1`);
  the general case inducts on the number of points with the same cover,
  cut by a vertical line between the two smallest points. Tau Ceti's
  `TauCeti.nonempty_fundamentalGroup_compl_mulEquiv_freeGroup` gives no
  generators and does not serve. The inverted ball circles are compared
  with these loops in the punctured discs that the balls cover, since
  both wind once about the centre, as in
  `TauCeti/AlgebraicTopology/ThricePuncturedSphere/ZeroOneGenerators.lean`
  (`Circle.homotopic_trans_of_degree_map_eq`).

The steps, in order (the step of each line can start once those it names
are merged):

| Step | Content | File | After | Size |
|---|---|---|---|---|
| 8a | Explicit balls of the sphere (a refactor) | `Surface/Genus.lean` | — | 100 |
| 8b | The plane minus finitely many positive reals: free basis of loops | `AlgebraicTopology/FundamentalGroup/PlaneMinusRealPoints.lean` | — | 350 |
| 8c | The same: the large circle as a product of the loops | `AlgebraicTopology/FundamentalGroup/PlaneMinusRealPoints.lean` | 8b | 250 |
| 8d | A pushout square in `GrpCat` as `Monoid.PushoutI` over `Bool` | `Algebra/Category/Grp/Pushout.lean` | — | 100 |
| 8e | `puncture`, the sum with `U`, `ballCircle`, the paths and the loops | `Surface/Puncture.lean` | 8a | 400 |
| 8f | The base case `g = 0` | `Surface/PuncturedSphere.lean` | 8b, 8c, 8e | 300 |
| 8g | The step, the induction and `fundamentalGroupMulEquiv` | `Surface/FundamentalGroup.lean` | 8d, 8e, 8f | 350 |

Step 8d first searches Mathlib and Tau Ceti for that comparison.

### `Geometry/Symplectic/Sum/RationalEllipticSurface.lean`

- `rationalEllipticSurface`, the set of Decision 4, a compact complex
  surface with charts from the atlas of bihomogeneous zero sets in
  `Geometry/Manifold/Projectivization/ProdZeroLocus/`; its projections to
  $\mathbb CP^2$ and $\mathbb CP^1$.
- `rationalEllipticSurface.symplecticForm` (Decision 5) with
  `isSymplectic_symplecticForm`.
- `fibreEmbedding`, the Fermat cubic over $[1:0]$, a symplectic embedding
  with a symplectic framing from the base; `torusDiffeomorph` from Tau
  Ceti's standard symplectic torus (Decision 8).
- `simplyConnectedSpace` (Decision 6) and
  `simplyConnectedSpace_compl_fibre` (Decision 7).

About 900 lines, in three issues.

### `Geometry/Symplectic/Sum/FundamentalGroup.lean`

- `fibreSum_fundamentalGroupMulEquiv`: for a connected symplectic
  four-manifold $X$, a symplectic embedding $\iota$ of Tau Ceti's standard
  symplectic torus (Decision 8) with a symplectic framing, and the fibre
  sum with $E(1)$, its form rescaled to match the area of $\iota$ and the torus identified by Moser
  (Decision 8), for any framing and admissible $\varepsilon$, $\delta$:
  $\pi_1(X')\cong\pi_1(X,\iota t_0)/\langle\!\langle\iota_*\pi_1(T^2,t_0)\rangle\!\rangle$,
  as `Subgroup.normalClosure` of the range of the induced map, and $X'$ is
  connected. By `TauCeti.isPushout_fundamentalGroup` for the two pieces,
  whose overlap is $T^2\times A(\delta,\varepsilon)$, with
  $\pi_1(E(1)\setminus T)=1$ from `RationalEllipticSurface.lean`, and the same
  theorem for $X$ covered by the complement of the closed tube and the open
  tube. Milestone: *Fundamental group after summing with the rational
  elliptic surface*.
- Its characteristic equation: on loops in the complement of the tube in
  $X$, based away from it, the isomorphism is induced by the inclusions of
  that complement into $X'$ and into $X$. Issue 11 needs it to sum along
  several tori one after another.

About 500 lines.

### `Geometry/Symplectic/Sum/FinitelyPresented.lean`

- The tori $T_i$ and the fibre torus of Decision 9 in
  `ClosedSurface g × (∀ i : Unit ⊕ Unit, AddCircle (p i))` with the product
  of an area form and `TauCeti.torusSymplecticForm p`, made pairwise
  disjoint by the small homotopies of Decision 9, symplectic, with
  symplectic framings.
- `exists_fundamentalGroup_mulEquiv`: every finitely presented $G$ is,
  up to isomorphism, $\pi_1$ of some compact, connected, boundaryless
  symplectic manifold of real dimension four. The proof sums $F\times T^2$
  with a separate $E(1)$ at every torus of the list, applying
  `fibreSum_fundamentalGroupMulEquiv` at each step.
  Milestone: *Gompf's realization of finitely presented groups*.

About 500 lines, in two issues.

## What the part uses

- *Almost complex spheres* (part 60): the sphere of dimension
  $2n\notin\{2,6\}$, $n\ne0$, has no almost complex structure (only
  `Pointwise.lean`).
- Merged: *Symplectic neighbourhoods*
  (`HasSymplecticTangentImages.exists_symplectomorphism_opens`), *Moser
  isotopy* (`exists_diffeotopy_mpullback_eq`), *Complex submanifolds*,
  *Complex projective space* (the Fubini–Study form and its taming), the
  smooth projective hypersurfaces (`SmoothProjectiveHypersurface.fermat`)
  and the first Chern class file's convention for paths of forms.
- Tau Ceti: `Geometry/Manifold/Gluing/`, `TopCat.GlueData` topology,
  `TauCeti.ConnectedSum` with its sphere and fundamental group files, van
  Kampen (`AlgebraicTopology/FundamentalGroup/VanKampen/`), wedge sums,
  surface groups, the uniformization of elliptic curves, holomorphic submersions,
  descent of forms, product symplectic forms.
- Mathlib: `Group.IsFinitelyPresented.exists_mulEquiv_presentedGroup`,
  `FundamentalGroup`, `SimplyConnectedSpace`, `Subgroup.normalClosure`.

## Building issues

In this order. All are sub-issues of #3287, *Build the part Symplectic
sums*. Sizes are estimates. "P60" is the issue of *Almost complex spheres*
(#3283 until it is split) that proves the nonexistence on spheres.

| # | Issue | Files | Blocked by | Size |
|---|---|---|---|---|
| 1 | Gluing two manifolds along open subsets | `Gluing/Pair.lean` | — | 400 |
| 2 | The annulus map and product collars | `Collar.lean` | — | 250 |
| 3 | Product neighbourhoods and the fibre sum; the milestone | `Fibre.lean` | 1, 2 | 500 |
| 4 | The pointwise obstruction | `Pointwise.lean` | P60 | 450 |
| 5 | The Hesse pencil surface and its symplectic form | `RationalEllipticSurface.lean` | — | 350 |
| 6 | Simple connectivity of $E(1)$ and of the fibre complement | `RationalEllipticSurface.lean` | 5 | 350 |
| 7 | The fibre as a standard torus | `RationalEllipticSurface.lean` | 5 | 300 |
| 8 | Closed surfaces of genus $g$ and their fundamental groups | `Surface/` | — | |
| 9 | The fundamental group of a sum with $E(1)$ | `FundamentalGroup.lean` | 3, 6, 7 | 500 |
| 10 | Tori in $F\times T^2$ | `FinitelyPresented.lean` | 3, 8 | 300 |
| 11 | Realization of finitely presented groups | `FinitelyPresented.lean` | 9, 10 | 250 |

Issues 1, 2, 5 and 8 can start at once, and issue 4 once P60 is merged.
The milestones are proved in issues 3, 4, 9 and 11.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd
  ed.][McDuffSalamon2017], §7.2: Exercise 7.2.1, Lemma 7.2.2, pp. 318–319,
  Exercise 7.2.6, Theorem 7.2.8.
* [R. E. Gompf, *A new construction of symplectic manifolds*][Gompf1995].
