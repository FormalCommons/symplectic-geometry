# Sphere bundles over surfaces

This is the detailed design of part 56 of `DESIGN.md`, *Sphere bundles over
surfaces*. It proves two milestones of `atlas/symplectic-fibrations.md`:
*Classification of oriented 2-sphere bundles over surfaces* and *Symplectic
classes on the nontrivial 2-sphere bundle over a surface*. Both follow
McDuff–Salamon [McDuffSalamon2017], §6.2: Lemma 6.2.3 and Exercise 6.2.4
for the first, Theorem 6.2.5 with Exercises 6.2.6, 6.2.8 and 6.2.9 for the
second. The input from differential topology is Smale's theorem
[Smale1959], from part 46. The handle induction follows Milnor's *Morse
theory* (1963), §3, and the de Rham Leray–Hirsch theorem follows Bott–Tu
[BottTu1982], §5.

All names below are in the namespace `SymplecticGeometry` unless they are
written with another one. Paths of new files are under `SymplecticGeometry/`.
Tau Ceti paths are relative to `.lake/packages/TauCeti/TauCeti/`. Every
merged declaration named below was checked against the library and Tau
Ceti `c9d170eed5a8`; names from parts 46, 48 and 50 are those of their
design files (`design/sphere-diffeomorphisms.md`,
`design/symplectic-fibrations.md`) or of `DESIGN.md`.

## Setting and notation

- **The base.** $B$ is `S : ClosedConnectedOrientedSurface` (the merged
  `Geometry/Manifold/VectorBundle/ChernNumber/Axioms.lean`), a closed
  connected surface over `𝓡 2` with an orientation `S.o`. Its genus is Tau
  Ceti's `TauCeti.surfaceGenus S`.
- **The fibre.** $S^2$ is `OnePoint ℂ` over `𝓘(ℝ, ℂ)`, as *Fibrations,
  connections and diffeomorphism groups* says, and $\mathrm{Diff}^+(S^2)$
  is part 46's `diffPlus`. The round sphere of part 46's `Smale.lean` is
  used only through part 46's transport of Smale's theorem to `OnePoint ℂ`.
- **Bundles.** An *oriented $S^2$-bundle* over `S` is a manifold `M` over a
  model `IM` of dimension four, a map `π : M → S` and a smooth atlas
  `A : TauCeti.MapFiber.Atlas (OnePoint ℂ) π` (`hA : A.IsContMDiff ∞ (𝓡 2)
  𝓘(ℝ, ℂ) IM`) with `A.HasStructureGroup diffPlus` (part 48,
  `StructureGroup.lean`). "Orientable" in the milestone means that such an
  atlas exists. No structure bundles these data: statements take them as
  arguments, as part 48 does.
- **Isomorphism over $B$.** Two bundles `π : M → S` and `π' : M' → S` are
  isomorphic when some `Φ : M ≃ₘ⟮IM, IM'⟯ M'` has `π' ∘ Φ = π`. This is
  written out where it is used, with no definition, since it has no API of
  its own beyond `Diffeomorph.trans` and `Diffeomorph.symm`.
- **The product** is `Prod.fst : S × OnePoint ℂ → S`, with the atlas
  `productAtlas S` whose every chart is the identity trivialization.
- **Circle bundles.** A principal circle bundle over `S` is, as in the
  merged `Geometry/Manifold/FiberBundle/Principal/CircleConnection.lean`,
  the unitary frame bundle `Fiber ℂ F V ℂ` of a Hermitian line bundle `V`.
  Its Euler number $e(P)$ is the first Chern number of `V`,
  `chernNumber (S.o.toHomologicalOrientation _) _ F V`, as
  `chernNumber_eq_integral_curvature` uses it. Only the parity of $e(P)$
  enters the classification, so its sign convention does not matter there.
- **Circle action on the fibre.** `Circle` acts on `OnePoint ℂ` by
  $u\cdot z=u^{-1}z$ on `ℂ` and fixes `∞`, so that the left action of
  `Circleᵐᵒᵖ` on frames and this action give Tau Ceti's associated bundle
  `TauCeti.AssociatedBundle Circle P (OnePoint ℂ)`. The action is the
  Möbius action of `diag(u⁻¹, 1)`, smooth by
  `OnePoint.instContMDiffConstSMulGLReal`; joint smoothness in `(u, z)` is
  a lemma of `SphereBundle/Basic.lean`.

## Decisions

These settle the points of *The design file decides* of part 56, and the
notes of the reviews of #2280 and #2445.

1. **The model of $X_B$.** The nontrivial bundle is
   `ruledSurface S := TauCeti.AssociatedBundle Circle P₁ (OnePoint ℂ)`,
   charted by `TauCeti.ManifoldTotalSpace`, for `P₁` the unitary frame
   bundle of the merged `Bundle.clutchingLineBundle φ 1` of
   `ChernNumber/Gluing.lean` with its metric `clutchingMetric`, for a
   coordinate disc `φ` of `S` fixed once (`CoordinateDisc.ofChart`). Its
   first Chern number is `1` (`Gluing.lean`). This is the model of
   Exercise 6.2.4, with the merged circle bundles and Euler numbers. It is
   smooth by `TauCeti.AssociatedBundle.contMDiffFiberBundle`, and an
   oriented $S^2$-bundle by part 48's bridge
   `TauCeti.ManifoldTotalSpace.mapFiberAtlas` and
   `TauCeti.AssociatedBundle.hasStructureGroup_mapFiberAtlas`, since the
   circle acts by Möbius maps, which lie in `diffPlus`
   (`mobiusSubgroup_le_diffPlus` of part 46).
   The second model, used only for part 3 of the second milestone, is the
   flat bundle of Exercises 6.2.8 and 6.2.9 (Decision 9). The blow-up of
   $\mathbb CP^2$ is not used. The two models are compared by the
   classification itself: the flat bundle is shown to be nontrivial, so it
   is isomorphic to `ruledSurface S`.
2. **No vector-bundle model.** Tau Ceti's `TauCeti.sphereBundle` and
   `TauCeti.AssociatedBundle.sphereBundleHomeomorph` give $P\times_{S^1}S^2$
   as the unit sphere bundle of $\underline{\mathbb R}\oplus V$, but only
   as a homeomorphism, and every step below reads $P\times_{S^1}S^2$
   through unit sections of $P$ instead. So they are not used.
3. **Classification by clutching, with Smale's theorem only for loops and
   paths.** The route is the clutching proof of `DESIGN.md`, in three
   steps.
   - *Triviality away from the maxima.* Take a Morse function `f` on `S`
     (`TauCeti.exists_isMorse`) and a regular value `a` above every
     critical value except those of the local maxima. Then every oriented
     $S^2$-bundle is trivial over `{f ≤ a}`, a compact surface whose
     complement is a finite union of small open discs `D i` around the
     maxima, each inside a Morse chart and inside the base set of a chart
     of the atlas. The proof is Milnor's handle induction: across a band
     `f⁻¹[c, c']` without critical values, the flow of a gradient-like
     field (as in `TauCeti.exists_sublevelHomotopyEquiv`), lifted to `M`
     by the horizontal lift of an Ehresmann connection (Tau Ceti's
     `IsSubmersion.exists_isEhresmannConnection`,
     `Submersion/EhresmannConnection.lean`), carries the bundle over
     `{f ≤ c'}` to the bundle over `{f ≤ c}`; an index-0 critical point adds
     a small disc, over which a chart of the atlas trivializes; an index-1
     point adds a band $[-1,1]\times[-1,1]$ along $\{\pm1\}\times[-1,1]$,
     and the trivialization extends across it exactly when a smooth map
     from $\{\pm1\}\times[-1,1]$ to `diffPlus` extends smoothly over the
     band. It does, since `diffPlus` is path connected (part 46,
     `pathConnectedSpace_roundDiffPlus` carried to `OnePoint ℂ`) and by the
     smoothing of Decision 4. No classification of surfaces is used, and
     the surface is never cut along curves: this answers the first point
     of the comment on #2393.
   - *Clutching loops.* On the boundary circle of each `D i`, the
     trivialization over `{f ≤ a}` and a chart over `D i` differ by a
     smooth loop in `diffPlus`. By Smale's theorem (π₁ of `diffPlus` is
     `Multiplicative (ZMod 2)`, and the inclusion of the rotations is a
     homotopy equivalence) the loop is homotopic to a rotation loop
     $\theta\mapsto(z\mapsto e^{i\varepsilon_i\theta}z)$ with
     $\varepsilon_i\in\{0,1\}$, after a constant factor that the chart over
     `D i` absorbs; Decision 4 makes the homotopy smooth, and a smooth
     homotopy of clutching loops on a collar gives an isomorphism of the
     glued bundles.
   - *Rotation clutching is a circle bundle.* The bundle glued by the
     rotation loops is $P\times_{S^1}S^2$ for the circle bundle glued by
     $e^{i\varepsilon_i\theta}$ at the same discs; its Euler number is
     $\sum_i\varepsilon_i$ by the merged disc clutching formula
     `Bundle.chernNumber_eq_sum_degree_clutching`, which allows finitely
     many discs. By `symplecticChernNumber_nonempty_iso_iff` the circle
     bundle is that of `clutchingLineBundle φ n`, $n=\sum_i\varepsilon_i$.
   So the several maxima need no Morse function with one maximum.
4. **Continuous homotopies made smooth.** A new file
   `Geometry/Diffeomorphism/Smoothing.lean` proves that a continuous map
   from a compact finite-dimensional manifold with corners `K` to
   `TauCeti.Diff IF F ∞` (weak Whitney topology), for compact boundaryless
   `F`, whose uncurried map `K × F → F` is smooth near a closed set `C`, is
   homotopic relative to `C` to one whose uncurried map is smooth. The
   proof embeds `F` in a Euclidean space (Tau Ceti's
   `SmoothEmbedding/Euclidean.lean`), smooths in the parameter by
   convolution in charts of `K` glued by a partition of unity, projects
   back by a tubular retraction, and uses that a map $C^1$-close to a
   diffeomorphism of a compact manifold is one. Tau Ceti's
   `TauCeti.SmoothEmbedding.exists_contMDiff_homotopyRel` is the model: it
   does the same for maps into a finite-dimensional manifold, with $C^0$
   control only, which does not keep the slices diffeomorphisms. Only
   `K = [0,1] × [0,1]` and `K = [0,1] × AddCircle 1` are needed, as the
   atlas's formalization note says, but the statement is general.
5. **The invariant that tells the two bundles apart** is the parity of the
   first Chern number of the vertical tangent bundle along a section. For
   a section `s` of an oriented $S^2$-bundle, $s^*\ker d\pi$ is an oriented
   plane bundle over `S`; with a fibre metric it is a
   `SymplecticSurfaceBundle S` of rank one, whose `symplecticChernNumber`
   mod 2 does not change under isomorphism over `S` (the derivative of
   $\Phi$ maps one vertical bundle to the other, preserving or reversing
   the orientation, and reversal negates the number). On the product a
   section is `(id, g)` and the number is
   $\deg g\cdot\chi(S^2)=2\deg g$, by `symplecticChernNumber_pullback` and
   `symplecticChernNumber_tangent`, with the fibre read as the round
   sphere over `𝓡 2` through part 46's `roundSphereDiffeomorph`, since
   `ClosedConnectedOrientedSurface` is modelled on `𝓡 2`; on $P\times_{S^1}S^2$ the section
   through the fixed point `0` has vertical bundle $V$ or its conjugate, of
   number $\pm e(P)$. This is the atlas's remark that the two bundles are
   told apart by the parity of the intersection form, read along one
   section, with no intersection form needed.
6. **$H^2(X_B;\mathbb R)$ and the coefficients $\mu_\pm$.** The sections
   $B_{\pm1}$ are the sections of `ruledSurface S` through the fixed points
   `0` and `∞` of the circle action, `poleSection S 0` and
   `poleSection S ∞`, chosen so that their self-intersections are $\pm1$
   (which of the two is $B_{+1}$ is fixed by the sign of $e(P_1)$ and is
   checked in issue 9). The coefficients of a class are read as the
   integrals over them, as `DESIGN.md` proposes:
   $\mu_\pm(\alpha)=\int_S s_\pm^*\alpha$ (`TauCeti.integralTopForm S.o`), a
   linear map `ruledCoefficients S : TauCeti.deRhamCohomology _ (ruledSurface S) 2 →ₗ[ℝ] ℝ × ℝ`,
   well defined by Stokes. This avoids Poincaré duality in the statement.
   "The class $a$ is represented by $\omega$" is `[ω] = a` in Tau Ceti's
   `deRhamCohomology`, and the milestone is stated for every class $a$, so
   it needs `ruledCoefficients S` to be injective, with
   $\langle a^2,[X_B]\rangle=\mu_+^2-\mu_-^2$ and
   $\langle a,[F]\rangle=\mu_+-\mu_-$.
7. **Leray–Hirsch in de Rham form, proved directly.** The singular
   Leray–Hirsch theorem of `AlgebraicTopology/Cohomology/LerayHirsch/`
   is not brought to de Rham classes: Tau Ceti's
   `deRhamCohomology.integration` lands in smooth singular cohomology, and
   neither library has the de Rham theorem in degree two, so the bridge
   would be longer than a direct proof. Instead, for an oriented
   $S^2$-bundle over `S` and a closed 2-form $\Theta$ with
   $\int_F\Theta=1$ on every fibre, every closed 2-form is cohomologous to
   $c\,\Theta+\pi^*\beta$, with $c=\int_F\alpha$, and $\pi^*\beta$ is exact
   exactly when $\int_S\beta=0$. The proof is the Mayer–Vietoris induction
   over a finite good cover of `S` subordinate to the base sets of the
   atlas (the library's `hasFiniteGoodCover_of_compactSpace`, with the
   induction pattern of `DeRham/SmoothFamily/GoodCover.lean`, on Tau Ceti's
   `DeRham/MayerVietoris.lean`), with the five lemma at each step. On a
   contractible `U` in a base set, $U\times S^2$ has the cohomology of
   $S^2$ by `TauCeti.deRhamCohomology.map_eq_of_homotopy` and
   `TauCeti.finrank_deRhamCohomology_sphere_self` (through
   `OnePoint.diffeomorphSphere`). On `S`, a top form with integral zero
   is exact by Tau Ceti's
   `mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero`. So the
   merged singular Leray–Hirsch files are not used, which corrects
   `DESIGN.md`.
8. **The form of Exercise 6.2.6 is Weinstein's form.** On
   $P\times_{S^1}S^2$ with a circle connection $A$ whose curvature is a
   constant multiple of an area form $\omega_S$ of `S` (the existence half
   of `chernNumber_eq_integral_curvature_and_exists`), part 50's
   `Fibration/Associated.lean` gives the closed form $\tau_A$ that
   restricts to $\lambda\,\omega_{FS}$ on each fibre, for the moment map
   $\lambda\mu$ of the rotation action, $\mu$ the height of Tau Ceti's
   `Geometry/Symplectic/Hamiltonian/MomentMap/FubiniStudy.lean`, in the
   page's sign. Then
   $\omega=\tau_A+K\pi^*\omega_S$ is nondegenerate exactly when
   $K+\lambda\mu f>0$ on the image of $\mu$, $f$ being the constant ratio
   of the curvature to $\omega_S$; this is checked by hand at each point,
   not through Thurston's theorem, so part 49 is not needed. The extreme
   values of $\mu$ are taken at the poles, so $\omega$ is symplectic
   exactly when both $\mu_\pm(\omega)>0$, and every pair
   $\mu_+>\mu_->0$ is reached by choosing $\lambda$ and $K$. This answers
   the note of the review of #2280: the form reuses part 50, which becomes
   a dependency of `RuledSurface.lean` (see *Departures*).
9. **The flat model of Exercise 6.2.9** is built without universal covers.
   For a surface of positive genus, Tau Ceti's
   `TauCeti.circlePeriodHom_surjective` gives smooth maps
   $u,v\colon S\to U(1)$ whose period homomorphisms reduce mod 2 to classes
   $a,b\in H^1(S;\mathbb Z/2)$ with $a\cup b\neq0$, from two integral classes
   whose cup product is one on $[S]$. They exist in positive genus by the
   library's Poincaré duality for compact oriented manifolds
   (`AlgebraicTopology/Cohomology/CompactSupport/Duality/Manifold.lean`,
   #810), over `ℤ` or over `ZMod 2`, whichever form it has. The real
   lines $\ell_u(x)=\mathbb R\sqrt{u(x)}\subset\mathbb C$ are flat line
   bundles, and the unit sphere bundle of $\ell_u\oplus\ell_v\oplus\ell_{uv}$
   is an $S^2$-bundle with locally constant transition functions in the
   Klein four-group of half-turns $\mathrm{diag}(\pm1,\pm1,\pm1)$, the
   commuting half-turns of Exercise 6.2.8. Read on `OnePoint ℂ` by
   `roundSphereDiffeomorph` of part 46, they are $z\mapsto\pm z$ and
   $z\mapsto\pm1/z$. The round area form descends to a closed form
   $\Theta_\rho$ restricting to the fibre forms, and
   $s\,\pi^*\omega_S+t\,\Theta_\rho$ is symplectic and compatible for all
   $s,t>0$, since the flat horizontal spaces are $\Theta_\rho$-null. Its
   coefficients are $\mu_\pm=s'\pm t'$ for positive multiples $s',t'$ of
   $s,t$, by Decision 7 (with $\Theta_\rho\wedge\Theta_\rho=0$ and
   $\int_F\pi^*\omega_S=0$), which covers $\mu_+>|\mu_-|$. Nontriviality
   is Decision 5 for a section of the sphere bundle, which exists by
   Tau Ceti's
   `Bundle.ContMDiffRiemannianMetric.exists_orthonormal_contMDiffSection_of_finrank_lt` (rank
   three over a surface); its vertical bundle is the orthogonal
   complement, whose first Chern number is $\langle a\cup b,[S]\rangle$
   mod 2. This is the largest computation of the part, and the one to
   check first.
10. **The corollary `IsOrientedCompatible.exists_hasStructureGroup_restrictsTo`
    of part 48 is not used**, which settles the note of the review of
    #2445. Part 1 of the second milestone needs only the fields of
    `IsOrientedCompatible` (the fibres are symplectic and positive, and
    $\omega^2$ is positive); parts 2 and 3 build their forms directly. So
    the part needs from part 48 only `MapFiber.lean`, `StructureGroup.lean`
    and `Basic.lean`, none of which waits for *Parallel transport*.

## Departures from `DESIGN.md`

`DESIGN.md` is corrected in the same pull request, in two places. In part
56, `RuledSurface.lean` reaches $H^2(X_B;\mathbb R)$ through the de Rham
Leray–Hirsch theorem of Decision 7, not through the merged singular
Leray–Hirsch files. *Builds on* and the build-order row gain part 50,
*Principal connections*, only for `Fibration/Associated.lean`, which
`RuledSurface.lean` uses (Decision 8). Part 50 is at level 0, so part 56
stays at level 2. Of part 48 the part uses `MapFiber.lean`,
`StructureGroup.lean` and `Basic.lean`, which `DESIGN.md` already allows.
The new blocker of the building issue is proposed in an issue.

## Files

### `Geometry/Diffeomorphism/Smoothing.lean`

- `ContinuousMap.exists_contMDiff_uncurry_homotopyRel_diff`: Decision 4.
  For `[CompactSpace F]`, `K` a compact manifold with corners,
  `γ : C(K, TauCeti.Diff IF F ∞)` and `C` closed with `γ` smooth on a
  neighbourhood of `C` (its uncurried map), there is `γ'` with smooth
  uncurried map and `γ.HomotopyRel γ' C`.
- The openness of diffeomorphisms among $C^1$ maps of a compact
  manifold, in the form the proof needs. The issue first searches Tau
  Ceti and Mathlib for it, and proves it only if both lack it.
- Corollaries for `diffPlus`-valued maps: a subgroup that is open and
  closed in `TauCeti.Diff` is preserved by small homotopies, and
  `diffPlus` is (orientation is locally constant).

About 450 lines; the issue may split the openness lemma off.

### `Geometry/Manifold/FiberBundle/SphereBundle/Basic.lean`

- `productAtlas S`, with `isContMDiff_productAtlas` and
  `hasStructureGroup_productAtlas` (every coordinate change is `1`).
- `OnePoint.circleAction`: the action of `Circle` on `OnePoint ℂ` by
  Möbius rotations, jointly smooth, by elements of `mobiusSubgroup`, and
  fixing `0` and `∞`; `rotationLoop n : AddCircle (2 * π) → diffPlus`.
- Gluing: for an atlas whose charts over an open `U` and over open discs
  differ on collars by smooth maps into `diffPlus`, smoothly homotopic
  clutching maps give isomorphic bundles over `S`
  (`exists_diffeomorph_of_homotopic_clutching`). The homotopy is cut off
  along the collar coordinate, as in the merged `ChernNumber/Gluing.lean`.

About 350 lines.

### `Geometry/Manifold/FiberBundle/SphereBundle/Clutching.lean`

- `exists_trivialization_sublevel`: Decision 3, first step; for an
  oriented $S^2$-bundle over a closed surface and `f`, `a` as there, a
  smooth trivialization over a neighbourhood of `{f ≤ a}` whose coordinate
  changes with the atlas lie in `diffPlus`. Split in two issues: the band
  step (flow lift) and the handle steps.
- `exists_rotationClutching`: Decision 3, second step: the bundle is
  isomorphic over `S` to the bundle glued from the product over `{f ≤ a}`
  and over the discs `D i` by `rotationLoop (ε i)`.
- `rotationClutching_iso_associated`: Decision 3, third step: that bundle
  is `TauCeti.AssociatedBundle Circle P (OnePoint ℂ)` for the circle bundle
  `P` of the line bundle clutched by $e^{i\varepsilon_i\theta}$, a
  finite-disc version of `clutchingLineBundle` added here (the merged one
  has one disc), with first Chern number $\sum_i\varepsilon_i$.

About 900 lines over three issues.

### `Geometry/Manifold/FiberBundle/SphereBundle/Classification.lean`

- `ruledSurface S` and its atlas (Decision 1), `poleSection S z` for
  `z = 0` and `z = ∞`.
- `associatedSphereBundle_iso_of_chernNumber_modEq`: if two Hermitian line
  bundles over `S` have Chern numbers of equal parity, their
  $P\times_{S^1}S^2$ are isomorphic over `S`. Both are read with two unit
  sections, over a disc and over its complement, as `clutchingLineBundle`
  is glued; $\theta\mapsto e^{in\theta}$ and $e^{i(n+2)\theta}$ differ by
  the loop $e^{2i\theta}$ of rotations, which is null-homotopic by an
  explicit smooth homotopy in `SU(2)` (the loop
  $\mathrm{diag}(e^{i\theta},e^{-i\theta})$ misses a point of
  $S^3$), acting by Möbius maps. No smoothing is needed here.
- `verticalChernNumber`: Decision 5, the number of the vertical bundle
  along a section, with `verticalChernNumber_modEq_of_diffeomorph`,
  `even_verticalChernNumber_prod` and
  `verticalChernNumber_poleSection` ($=\pm e(P)$).
- The milestone,
  `nonempty_diffeomorph_prod_or_ruledSurface_and_associated_iff_even`:
  for every oriented $S^2$-bundle over `S`, it is isomorphic over `S` to
  exactly one of `Prod.fst` and `ruledSurface S`; and for every
  Hermitian line bundle `V` over `S`,
  `TauCeti.AssociatedBundle Circle (Fiber ℂ F V ℂ) (OnePoint ℂ)` is
  isomorphic over `S` to the product exactly when its Chern number is
  even. Its docstring ends with "Milestone: *Classification of oriented
  2-sphere bundles over surfaces*." The issue splits the statement into
  named conjuncts if one theorem reads badly.

About 500 lines.

### `Geometry/Manifold/DeRham/SphereBundle.lean`

- `exists_sub_mem_exactForms_smul_add_mpullback`: Decision 7, for an
  oriented $S^2$-bundle over `S` and a closed $\Theta$ with fibre
  integral `1`.
- `mpullback_mem_exactForms_iff_integralTopForm_eq_zero`.
- `finrank_deRhamCohomology_two_sphereBundle : … = 2`.
- `integralTopForm_wedge_mpullback`: $\int\Theta\wedge\pi^*\beta=(\int_F\Theta)(\int_S\beta)$.
  The form $\beta$ is cohomologous to one supported in a disc over which
  the bundle is trivial. There $\Theta$ is cohomologous to the pull-back
  of its restriction to a fibre, and the integral of
  $\mathrm{pr}_1^*\beta\wedge\mathrm{pr}_2^*\gamma$ over a product splits.
  The issue proves that splitting for Tau Ceti's `integralTopForm` if it
  is missing.

About 450 lines; the induction is one issue.

### `Geometry/Symplectic/RuledSurface.lean`

- `ruledCoefficients S` (Decision 6), `ruledCoefficients_injective`,
  `integralTopForm_wedge_self_eq` ($\mu_+^2-\mu_-^2$) and
  `integral_fiber_eq` ($\mu_+-\mu_-$). By Decision 7 it is enough to
  check them on $\pi^*\omega_S$ and on $\Theta=\tau_A$ (normalized).
  The pull-back of $\tau_A$ along a pole section is $\lambda\mu(p)F_A$,
  where $p$ is the pole. Away from the poles
  $\omega_{FS}=d\mu\wedge d\theta$, so $\tau_A$ is exact there, and
  $\int\tau_A\wedge\tau_A$ and $\int_F\tau_A$ come from Stokes's
  theorem on the complement of small neighbourhoods of the two pole
  sections. The term $\int\Theta\wedge\pi^*\beta=(\int_F\Theta)(\int_S\beta)$
  is a lemma of issue 8.
- Part 1, `ruledCoefficients_abs_lt_of_isOrientedCompatible`: if
  `ω` with `A.IsOrientedCompatible hA S.o oF ω` (part 48) for the atlas of
  `ruledSurface S` has class `a`, then $|\mu_-|<\mu_+$.
- Part 2, `exists_isOrientedCompatible_of_lt_of_pos` (Decision 8).
- Part 3, `exists_isOrientedCompatible_of_abs_lt` for
  `0 < surfaceGenus S` (Decision 9), transported to `ruledSurface S` along
  the isomorphism of the classification. That isomorphism can be taken to
  preserve the fibre orientations: if it does not, compose it with complex
  conjugation on the fibres of the flat model, which commutes with the
  half-turns. The classes are compared through $\int_F a$ and
  $\int a\wedge a$, which the isomorphism preserves. They determine
  $\mu_\pm$: $\mu_+-\mu_-=\int_F a>0$ and
  $\mu_++\mu_-=\int a\wedge a/\int_F a$. So no section of the flat model
  has to be integrated over.
- The milestone, `isOrientedCompatible_ruledSurface`: the three parts
  together. Its docstring ends with "Milestone: *Symplectic classes on the
  nontrivial 2-sphere bundle over a surface*."

The orientation `oF` of `OnePoint ℂ` is `TauCeti.complexManifoldOrientation`.
About 800 lines; the flat model goes to a file
`Geometry/Symplectic/RuledSurface/Flat.lean` if it is longer than the
estimate, and `RuledSurface.lean` becomes `RuledSurface/Basic.lean`.

## What the part uses

- Part 46: `diffPlus`, `mobiusSubgroup_le_diffPlus`,
  `roundSphereDiffeomorph`, `exists_homotopyRel_specialOrthogonal_roundDiffPlus`,
  `pathConnectedSpace_roundDiffPlus` and
  `roundDiffPlusFundamentalGroupMulEquiv`, carried to `OnePoint ℂ` along
  `map_diffPlus_diffCongr`.
- Part 48: `TauCeti.MapFiber.Atlas.IsContMDiff`, `HasStructureGroup`,
  `CoordChangeMem`, the bridge `mapFiberAtlas` with
  `hasStructureGroup_mapFiberAtlas`, `RestrictsTo` and
  `IsOrientedCompatible`.
- Part 50: Weinstein's form on $P\times_{S^1}S^2$
  (`Fibration/Associated.lean`), for `Circle`.
- The merged *First Chern number*: `ClosedConnectedOrientedSurface`,
  `SymplecticSurfaceBundle` with `symplecticChernNumber_nonempty_iso_iff`,
  `symplecticChernNumber_pullback` and `symplecticChernNumber_tangent`,
  `clutchingLineBundle`, `chernNumber_eq_sum_degree_clutching`,
  `unitFrame`, and `chernNumber_eq_integral_curvature_and_exists`.
- The library's finite good covers (`DeRham/GoodCover/Compact.lean`).
- Tau Ceti: Morse functions and sublevel deformations
  (`Geometry/Manifold/Morse/`), Ehresmann connections, associated bundles,
  de Rham cohomology (Mayer–Vietoris, homotopy invariance, spheres, top
  degree), smooth approximation, circle-valued maps with prescribed
  periods, and orthonormal sections of bundles of rank above the
  dimension.

## Building issues

In this order. All are sub-issues of #2396, *Build the part Sphere bundles
over surfaces*. Sizes are estimates. "P46-8", "P46-9" are issues 8 and 9 of
`design/sphere-diffeomorphisms.md` (#2383 until it is split); "P48-n" is
issue `n` of `design/symplectic-fibrations.md`; "P50" is the issue of
*Principal connections* (#2375 until it is split) that builds
`Fibration/Associated.lean`.

| # | Issue | Files | Blocked by | Size |
|---|---|---|---|---|
| 1 | Smoothing families of diffeomorphisms | `Smoothing.lean` | — | 450 |
| 2 | The product, the rotation action and gluing | `SphereBundle/Basic.lean` | P48-2 | 350 |
| 3 | Bundles across bands without critical points | `Clutching.lean` | 2 | 300 |
| 4 | Handles of index 0 and 1; triviality away from the maxima | `Clutching.lean` | 1, 3; P46-9 | 350 |
| 5 | Clutching loops and the finite-disc line bundle | `Clutching.lean` | 4 | 300 |
| 6 | Parity of Euler numbers and the vertical invariant | `Classification.lean` | 2 | 300 |
| 7 | The classification | `Classification.lean` | 5, 6 | 200 |
| 8 | De Rham Leray–Hirsch for $S^2$-bundles | `DeRham/SphereBundle.lean` | P48-2 | 450 |
| 9 | $H^2(X_B)$, the coefficients and part 1 | `RuledSurface.lean` | 7, 8; P48-3; P50 | 350 |
| 10 | Part 2: Weinstein's form | `RuledSurface.lean` | 9 | 250 |
| 11 | The flat model and part 3; the milestone | `RuledSurface.lean` | 9 | 450 |

Issues 1, 6 (once P48-2 is merged) and 8 can start in parallel. The
milestones are proved in issues 7 and 11.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd
  ed.][McDuffSalamon2017], §6.2: Lemma 6.2.3, Exercise 6.2.4,
  Theorem 6.2.5, Exercises 6.2.6, 6.2.8 and 6.2.9.
* [S. Smale, *Diffeomorphisms of the 2-sphere*][Smale1959].
* [R. Bott, L. W. Tu, *Differential Forms in Algebraic
  Topology*][BottTu1982], §5 (the Mayer–Vietoris argument) and §14
  (Leray–Hirsch).
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton
  University Press, 1963, §3 (handles).
