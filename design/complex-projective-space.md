# Complex projective space

This is the detailed design of part 27 of `DESIGN.md`, *Complex projective
space*. It covers the milestone *Fubini–Study form on complex projective
space* of `atlas/almost-complex-structures.md`, and the last sentence of the
milestone *Complex submanifolds of Kähler manifolds* (the case of
$\mathbb CP^n$). The milestone follows McDuff–Salamon [McDuffSalamon2017],
Example 4.3.3, Exercise 4.3.4(i)–(iv) and Exercise 4.3.5(i), p. 168–169; the
local potentials and the Dolbeault calculus are those of Huybrechts,
*Complex Geometry*, §§1.3 and 3.1, which Tau Ceti's Dolbeault files cite, and
the affine charts those of Griffiths–Harris [GriffithsHarris1978], Chapter 0,
§§1–2.

All names below are in the namespace given with them; a name written without
one is in `SymplecticGeometry`. Paths of new files are under
`SymplecticGeometry/`; Tau Ceti paths are relative to
`.lake/packages/TauCeti/TauCeti/`, as in `DESIGN.md`. Throughout, `n : ℕ`,
and $\mathbb CP^n$ is `ℙ ℂ (Fin (n + 1) → ℂ)` with Tau Ceti's charts
(`Geometry/Manifold/Instances/Projectivization.lean`), read as a real
manifold through `Projectivization.instIsManifoldReal`, so modelled on
`𝓘(ℝ, Fin n → ℂ)`. Its almost complex structure is
`J_P := TauCeti.SmoothAlmostComplexStructure.ofComplexManifold (Fin n → ℂ)
(ℙ ℂ (Fin (n + 1) → ℂ))`.

## What exists, and what the part adds

Tau Ceti already has:

- the complex manifold $\mathbb CP^n$: the affine charts
  `Projectivization.affineChart`, `affineOpen`,
  `affineOpenPartialHomeomorph`, their smoothness
  (`contMDiffOn_affineChart`, `contMDiff_affineChart_symm`), the criteria
  `Projectivization.contMDiff_of_contDiffOn_mk` and
  `contMDiffAt_of_eventually_eq_mk`, maps induced by linear maps
  (`Projectivization.map`, `contMDiff_map`, `mapDiffeomorph`,
  `isSmoothEmbedding_map`, in `Geometry/Manifold/Projectivization/Map.lean`),
  the affine coordinates of $\mathbb CP^1$ (`TauCeti.ProjectiveLine.affineParam`),
  and change of field `Projectivization.mapProjective`
  (`LinearAlgebra/Projectivization/BaseChange.lean`);
- `SmoothAlmostComplexStructure.ofComplexManifold` with
  `nijenhuis_ofComplexManifold`, and the Dolbeault operators `del`,
  `delBar`, `dC` with `del_apply_apply`, `delBar_apply_apply`,
  `mextDerivₗ_eq_del_add_delBar_of_nijenhuis_eq_zero` and
  `covectorComplexStructure` ($a\mapsto-a\circ J$ on real one-forms), in
  `Geometry/Manifold/DifferentialForm/Dolbeault/` and
  `DifferentialForm/AlmostComplexType.lean`;
- descent of forms: `TauCeti.RoughForm.isBasic_of_mpullback_eq`
  (invariant forms that kill vertical vectors are basic,
  `Geometry/Manifold/DifferentialForm/Pullback/Descent.lean`),
  `TauCeti.SmoothForm.descendedForm`, `mpullback_descendedForm`,
  `eq_descendedForm_iff` (`Pullback/Submersion.lean`), and
  `TauCeti.SmoothTwoForm.existsUnique_isSymplectic_mpullback_eq`,
  `eval₂_descendedForm_mfderiv`, `isSymplectic_descendedForm_iff`
  (`Geometry/Symplectic/Manifold/Descent.lean`); submersions from surjective
  derivatives, `ContMDiff.isSubmersionOfComplement_of_surjective_mfderiv`
  (`Geometry/Manifold/Submersion/Split.lean`);
- on the unit sphere of a symplectic inner product space:
  `TauCeti.SymplecticForm.sphereContactForm` with
  `mextDeriv_sphereContactForm_apply` (its derivative is the restriction of
  the linear form), `TauCeti.SymplecticForm.constSmooth` (a linear
  symplectic form as a constant two-form) and `radialPrimitive`;
- on $\mathbb CP^1$: `OnePoint.fubiniStudyForm`, of total area $1$, with
  `eval₂_fubiniStudyForm_coe`, `isSymplectic_fubiniStudyForm`,
  `compatible_fubiniStudyForm`, and `OnePoint.diffeomorphProjectivization`;
  the diffeomorphism `OnePoint.diffeomorphSphere v ι` from the Riemann
  sphere onto the unit sphere, whose inverse is stereographic projection
  from `v` (`diffeomorphSphere_symm_apply_of_ne`), with
  `OnePoint.inner_mfderiv_diffeomorphSphere` (the round metric is $4\pi$
  times the Fubini–Study metric); and `Diffeomorph.restrictScalars`
  (`Geometry/Manifold/Diffeomorph/RestrictScalars.lean`);
- the punctured space `TauCeti.puncturedSpace V : Opens V`, the set
  $\{0\}^c$, with `mem_puncturedSpace`
  (`Geometry/Manifold/Instances/Cylinder.lean`);
- integration: `TauCeti.integralTopForm`,
  `integralTopForm_mpullback_of_isOrientationPreservingAt`, the canonical
  orientation `TauCeti.complexManifoldOrientation` of a complex manifold
  with `Manifold.Orientation.reindex`, and the area of the round sphere,
  `Orientation.integralTopForm_sphereOrientation_sphereVolumeForm`
  ($4\pi$, `Geometry/Manifold/DifferentialForm/Integration/UnitSphere.lean`);
- Lagrangian embeddings `TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianEmbedding`
  with `IsIsotropicMap.isLagrangianEmbedding_of_finrank`, and the torus
  `ι → AddCircle p` with its charts (`Geometry/Manifold/Instances/AddCircle.lean`,
  `AddCircle/Torus.lean`).

Tau Ceti has no Fubini–Study form for $n\ge2$, no $\rho_{\mathrm{FS}}$, no
smooth Hopf map, no integral of a form over $\mathbb CP^1$, and none of the
Darboux charts or Lagrangian examples (the correspondence list of
`atlas/almost-complex-structures-lean.md`, rows 4.3.3–4.3.5, says the same).
This part adds them.

## Decisions

### The models

- **$\mathbb CP^n$** is `ℙ ℂ (Fin (n + 1) → ℂ)`, as `DESIGN.md` fixes. The
  part defines no abbreviation for it.
- **$\mathbb C^{n+1}\setminus0$** is the open subset
  `TauCeti.puncturedSpace (Fin (n + 1) → ℂ)` of `Fin (n + 1) → ℂ`,
  an open submanifold of a complex vector space, hence a complex manifold.
  This is where $\rho_{\mathrm{FS}}$ and $\alpha_{\mathrm{FS}}$ live: the
  page states $\rho_{\mathrm{FS}}$ through $\partial\bar\partial$, and Tau
  Ceti's Dolbeault identities hold for `ofComplexManifold`. The projection
  is `Projectivization.mk`, which is how Tau Ceti's charts are built, so no
  coordinate change is needed. The sup norm of `Fin (n + 1) → ℂ` plays no
  role: $\lvert z\rvert^2$ is written as `∑ i, ‖z i‖ ^ 2`, and $\omega_0$ on
  it is Tau Ceti's `stdComplexPiSymplecticForm (Fin (n + 1))`, which
  `complexToRealEuclidean` carries to `stdForm`.
- **The sphere and the ball** are in `StdSpace`, as the conventions of
  `DESIGN.md` ask for metric statements: $S^{2n+1}$ is
  `sphere (0 : StdSpace (Fin (n + 1))) 1`, with Mathlib's charts modelled on
  `𝓡 (2 * n + 1)`, and $B$ is `Metric.ball (0 : StdSpace (Fin n)) 1`. The
  restriction of $\omega_0$ is then `stdForm` read on the sphere, Tau Ceti's
  `sphereContactForm` applies to it with no transport, and the Darboux
  charts land in the model of the linear theory, so that "symplectomorphic
  to the ball in $(\mathbb R^{2n},\omega_0)$" uses `stdForm` itself. The
  model `EuclideanSpace ℂ` of Tau Ceti's sphere quotient is not used; the
  part needs neither that quotient nor its homeomorphism with
  `ℙ ℂ (Fin (n + 1) → ℂ)`.

### The route

The page's advice is followed: the form is built on the sphere and descends.

1. On $\mathbb C^{n+1}\setminus0$, $\alpha_{\mathrm{FS}}$ is defined as the
   pull-back of Tau Ceti's `sphereContactForm` along the radial projection
   $\varphi$, with the value $\alpha_z(v)=\omega_0(z,v)/(2\lvert z\rvert^2)$ as a
   lemma, and
   $\rho_{\mathrm{FS}}:=d\alpha_{\mathrm{FS}}$. So part 1's first identity
   holds by definition, and the others are theorems: the explicit value of
   $\rho_{\mathrm{FS}}$, the potential identity
   $\alpha_{\mathrm{FS}}=\tfrac14 J^*(d\log\lvert z\rvert^2)$ (with $J^*$
   Tau Ceti's `covectorComplexStructure`, so $-\tfrac14\,d\log\lvert z\rvert^2\circ J$),
   the $\partial\bar\partial$ form, and $\rho_{\mathrm{FS}}=\varphi^*\sigma$
   for the radial projection $\varphi$.
2. On the sphere, $\sigma$ is the pull-back of `(stdForm _).constSmooth`
   along the inclusion. It is closed, being $d$ of `sphereContactForm`. It
   is invariant under the circle, kills the generator $J_0x$, and its kernel
   at $x$ is exactly $\mathbb R J_0x$, the kernel of the derivative of the
   Hopf map. So it is basic (`isBasic_of_mpullback_eq`, with the circle
   acting by $x\mapsto\cos t\,x+\sin t\,J_0x$), and `fubiniStudyForm` is
   defined as `SmoothForm.descendedForm` along the sphere Hopf map. It is
   symplectic by `isSymplectic_descendedForm_iff`.
3. The projection from $\mathbb C^{n+1}\setminus0$ is the sphere Hopf map
   after $\varphi$, so its pull-back of `fubiniStudyForm` is
   $\varphi^*\sigma=\rho_{\mathrm{FS}}$; uniqueness holds because pull-back
   along a surjective submersion is injective (`eq_descendedForm_iff`).
4. Invariance, compatibility, the normalization, the Darboux charts and the
   Lagrangian examples are all checked upstairs, on $\rho_{\mathrm{FS}}$ or
   $\sigma$, and read downstairs through the eval lemma of the descent.

### Unitary invariance, in a form that also gives lines

Invariance is proved once for every matrix with orthonormal columns:
`A : Matrix (Fin (n + 1)) (Fin (m + 1)) ℂ` with `Aᴴ * A = 1` induces
$\mathbb CP^m\to\mathbb CP^n$, and its pull-back of the Fubini–Study form of
$\mathbb CP^n$ is that of $\mathbb CP^m$, since $A$ preserves
$\lvert z\rvert^2$, $\operatorname{Re}\langle z,v\rangle$ and $\omega_0$. For
`m = n` this is the action of $\mathrm U(n+1)$; for the inclusion of the
first two coordinates it says that the form restricts to the coordinate line
as the form of $\mathbb CP^1$.

### The normalization and the area of a line

- **The affine formula** is stated in Tau Ceti's coordinate
  `ProjectiveLine.affineParam 0`, $t\mapsto[1:t]$: the pull-back evaluates
  as $\operatorname{Im}(\bar vw)/(1+\lvert t\rvert^2)^2$, which is
  $dx\wedge dy/(1+x^2+y^2)^2$ in the form of Tau Ceti's
  `OnePoint.eval₂_fubiniStudyForm_coe`. The comparison with Tau Ceti's form
  is `mpullback (diffeomorphProjectivization ℂ ∞) (fubiniStudyForm 1) =
  π • OnePoint.fubiniStudyForm`; both sides have the same density up to the
  factor $\pi$ in each chart.
- **The stereographic map.** The page's formula $[1+x_3:x_1+ix_2]$ has both
  entries zero at the south pole $(0,0,-1)$, so it defines the map only on
  the sphere without that point. Because $(1+x_3)(1-x_3)=x_1^2+x_2^2$, it
  agrees there with $[x_1-ix_2:1-x_3]$, which is defined except at the north
  pole. The part does not define the map by cases, since Tau Ceti has it
  as a composite of two diffeomorphisms: `sphereToProjectiveLine` is
  `(OnePoint.diffeomorphSphere v ι).symm` followed by
  `OnePoint.diffeomorphProjectivization ℂ ω` read on the real structures
  (`Diffeomorph.restrictScalars ℝ`), with `v` the north pole $(0,0,1)$ and
  `ι z = (Re z, -Im z, 0)`. Off `v` the first factor is
  $(x_1-ix_2)/(1-x_3)$ by `diffeomorphSphere_symm_apply_of_ne`, and the
  second sends $t$ to $[t:1]$ and $\infty$ to $[1:0]$, so the composite is
  $[x_1-ix_2:1-x_3]$ off the north pole, and $[1+x_3:x_1+ix_2]$ off the
  south pole. Both formulas are lemmas; smoothness, bijectivity and the
  smooth inverse come with the diffeomorphism. The page's statement is the
  first formula where it makes sense, so no entry in `ERRATA.md` is needed.
  The pull-back identity is
  `mpullback sphereToProjectiveLine (fubiniStudyForm 1) = (4 : ℝ)⁻¹ • o₃.sphereVolumeForm`
  for the standard orientation `o₃` of `EuclideanSpace ℝ (Fin 3)`, whose
  `sphereVolumeForm` is the area form of the round sphere for the outward
  normal. The sign is $+$: inverse stereographic projection from the south
  pole, which Tau Ceti's `UnitSphere.lean` shows to be positively oriented
  with Jacobian density $4/(1+x^2+y^2)^2$, is the inverse of the affine
  coordinate $w=(x_1+ix_2)/(1+x_3)$.
- **The area of a line** is an integral of a top form over Tau Ceti's
  oriented $\mathbb CP^1$: with
  `oCP1 := (TauCeti.complexManifoldOrientation (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))).reindex (finCongr h)`,
  `h : 2 * finrank ℂ (Fin 1 → ℂ) = 2`, a line is the image of
  `Projectivization.map f hf` for an injective
  `f : (Fin 2 → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)`, and its area is
  `TauCeti.integralTopForm oCP1 (mpullback (map f hf) (fubiniStudyForm n)).val`.
  It is $\pi$: on $\mathbb CP^1$ itself by change of variables along
  `sphereToProjectiveLine` and the $4\pi$ of the round sphere; for every
  line by writing $f=A\circ g$ with $A$ with orthonormal columns
  (Gram–Schmidt) and $g\in\mathrm{GL}_2(\mathbb C)$, the invariance above,
  and invariance of the integral under the biholomorphism `map g` of
  $\mathbb CP^1$, which preserves the canonical orientation. The page's
  sentence that every line has area $\pi$ is this theorem. No `rfl`
  identifies `Fin (2 * finrank ℂ (Fin 1 → ℂ))` with `Fin 2`, hence the
  reindexing.

### Statements in the page's conventions

- The page's $\omega_0$ is `stdForm` on `StdSpace` and
  `stdComplexPiSymplecticForm` on `Fin (n + 1) → ℂ`, which agree along
  `complexToRealEuclidean` by the definition of `stdForm`. Both are
  $\sum_jdx_j\wedge dy_j$, positive on $(v,iv)$, as `DESIGN.md` fixes.
- Compatibility is Tau Ceti's `SmoothTwoForm.Compatible` with `J_P`, so
  $g(v,w)=\omega_{\mathrm{FS}}(v,J_Pw)$, the page's metric.
- $\tfrac i2\partial\bar\partial f$ is written
  `(Complex.I / 2) • J.del (J.delBar f)` on the complexified function, with
  `J` the structure of the complex manifold, and its real form
  $\tfrac14\,d(J^*df)$. The general identity between the two, for a real
  function and an almost complex structure with $N_J=0$, is a lemma of Tau
  Ceti's Dolbeault calculus, not of $\mathbb CP^n$; it goes in its own file
  `Geometry/Manifold/DifferentialForm/Dolbeault/Potential.lean`, in Tau
  Ceti's namespace `TauCeti.SmoothAlmostComplexStructure`.
- The Darboux charts are `PartialDiffeomorph`s, as in the library's and Tau
  Ceti's Darboux theorems, with the pull-back stated pointwise through
  `mvfderiv`, as `exists_darbouxChart_mvfderiv_eq_of_isInteriorPoint` does.
- $\mathbb RP^n\subset\mathbb CP^n$ is the image of Tau Ceti's
  `Projectivization.mapProjective Complex.ofRealHom` on
  `ℙ ℝ (Fin (n + 1) → ℝ)` with its real charts. The Clifford torus is the
  image of $\theta\mapsto[1:e^{i\theta_1}:\dots:e^{i\theta_n}]$ on
  `Fin n → AddCircle (2 * π)`, through `AddCircle.toCircle`; its range is
  proved to be the page's set $\{\lvert z_0\rvert=\dots=\lvert z_n\rvert\}$.
- Dimension zero needs no case: $\mathbb CP^0$ is a point, the sphere is a
  circle, the ball in `StdSpace (Fin 0)` is a point, and the statements hold
  as stated. There is no line in $\mathbb CP^0$, so the area statement is
  vacuous there.

### The milestone as theorems

Each part of the milestone is a theorem of its own, in the file of its
subject, and the milestone is also one theorem, `fubiniStudyForm_spec`, the
conjunction of the parts' statements, in `Lagrangian.lean`, the last file,
which imports the others. Only `fubiniStudyForm_spec` carries the milestone
line in its docstring. The last sentence of *Complex submanifolds of Kähler
manifolds* is `isKahler_mpullback_fubiniStudyForm` in `Kahler.lean`, with its
own milestone line.

### Placement

- `Hopf.lean` is general projective-space material (the approving review of
  #838 asked for it to leave `FubiniStudy/`). It goes to
  `Geometry/Manifold/Projectivization/Hopf.lean`, beside Tau Ceti's files in
  that folder; Tau Ceti has no file of that name there.
- The other files stay in `Geometry/Manifold/Projectivization/FubiniStudy/`,
  as `DESIGN.md` says. Tau Ceti has no `FubiniStudy.lean` in that folder.
- `DESIGN.md`'s list of the part's files is updated for both changes.

## Files and declarations

### `Geometry/Manifold/DifferentialForm/Dolbeault/Potential.lean`

In namespace `TauCeti.SmoothAlmostComplexStructure`, for a manifold with a
smooth almost complex structure `J` and a smooth real function `f` (as a
real `0`-form, complexified by `SmoothForm.mapCoeff Complex.ofRealCLM`):

- `dC_mapCoeff_ofReal`: $d^cf=-\,df\circ J$, that is, the complexification
  of `J.covectorComplexStructure (d f)`; from `del_apply_apply` and
  `delBar_apply_apply`, with no hypothesis on `J`.
- `del_delBar_mapCoeff_ofReal_of_nijenhuis_eq_zero (hJ : J.nijenhuis = 0)`:
  `(Complex.I / 2) • J.del (J.delBar f)` is the complexification of
  `(4 : ℝ)⁻¹ • d (J.covectorComplexStructure (d f))`; through
  `mextDerivₗ_eq_del_add_delBar_of_nijenhuis_eq_zero` and
  `mextDerivₗ_dC_of_mextDerivₗ_eq_del_add_delBar`.

Reference: Huybrechts, *Complex Geometry*, §§1.3 and 3.1.

### `Geometry/Manifold/Projectivization/Hopf.lean`

In namespace `Projectivization`, for `𝕜` a nontrivially normed field that is
a normed `ℝ`-algebra and finite-dimensional over `ℝ` (so `ℝ` and `ℂ`), and
the real structures of Tau Ceti (`instIsManifoldReal`):

- `mkNonzero 𝕜 n : TauCeti.puncturedSpace (Fin (n + 1) → 𝕜) → ℙ 𝕜 (Fin (n + 1) → 𝕜)`,
  $v\mapsto[v]$, with `mkNonzero_apply` and `surjective_mkNonzero`.
- `contMDiff_mkNonzero` (every order), `isSubmersion_mkNonzero`
  (`IsSubmersion 𝓘(ℝ, Fin (n + 1) → 𝕜) 𝓘(ℝ, Fin n → 𝕜) ∞`), from the local
  sections $z\mapsto$ `Fin.insertNth j 1 z` over the affine charts and
  `ContMDiff.isSubmersionOfComplement_of_surjective_mfderiv`.
- `ker_mfderiv_mkNonzero`: the kernel at $v$ is the real subspace
  `(𝕜 ∙ (v : _)).restrictScalars ℝ`, by invariance under scalars and
  dimension.

In namespace `SymplecticGeometry`:

- the instance `fact_finrank_stdSpace_fin_succ : Fact (finrank ℝ (StdSpace
  (Fin (n + 1))) = 2 * n + 1 + 1)`, which Mathlib's charts on the sphere need,
  is a scoped instance of *Standard model*, placed with `StdSpace` in
  `LinearAlgebra/Symplectic/Standard/Basic.lean`; this file uses it.
- `sphereHopf n : sphere (0 : StdSpace (Fin (n + 1))) 1 → ℙ ℂ (Fin (n + 1) → ℂ)`,
  $x\mapsto[(\texttt{complexToRealEuclidean})^{-1}x]$, with
  `sphereHopf_apply`, `contMDiff_sphereHopf`, `surjective_sphereHopf`,
  `isSubmersion_sphereHopf`, `sphereHopf_eq_sphereHopf_iff` (two points have
  the same image exactly when $y=\cos t\,x+\sin t\,J_0x$ for some $t$), and
  `ker_mfderiv_sphereHopf`: read in `StdSpace` through the derivative of the
  inclusion, the kernel at $x$ is `ℝ ∙ stdComplexStructure _ x`.
- `radialProjection n : TauCeti.puncturedSpace (Fin (n + 1) → ℂ) → sphere (0 :
  StdSpace (Fin (n + 1))) 1`, $z\mapsto\hat z/\lVert\hat z\rVert$ with
  $\hat z=$ `complexToRealEuclidean _ z`, with `radialProjection_apply`,
  `contMDiff_radialProjection`, and `sphereHopf_comp_radialProjection :
  sphereHopf n ∘ radialProjection n = mkNonzero ℂ n`.

Reference: Griffiths–Harris, Chapter 0, §1.

### `Geometry/Manifold/Projectivization/FubiniStudy/Basic.lean`

With `Z := TauCeti.puncturedSpace (Fin (n + 1) → ℂ)`, `J_Z` its `ofComplexManifold`,
$\lvert z\rvert^2=\sum_i\lVert z_i\rVert^2$ and
$\omega_0=$ `stdComplexPiSymplecticForm (Fin (n + 1))`:

- `fubiniStudyPrimitive n : TauCeti.SmoothForm 𝓘(ℝ, Fin (n + 1) → ℂ) Z ℝ 1`,
  with `fubiniStudyPrimitive_apply`: $\alpha_z(v)=\omega_0(z,v)/(2\lvert z\rvert^2)$.
- `fubiniStudyPotential n : TauCeti.SmoothForm 𝓘(ℝ, Fin (n + 1) → ℂ) Z ℝ 0`, the
  function $f=\log\lvert z\rvert^2$, with `fubiniStudyPotential_apply`.
- `fubiniStudyPrimitive_eq`: $\alpha_{\mathrm{FS}}=\tfrac14\,J_Z^*\,d\log\lvert z\rvert^2$
  (`(4 : ℝ)⁻¹ • J_Z.covectorComplexStructure (d f)`, `f = fubiniStudyPotential n`).
- `fubiniStudyLift n : TauCeti.SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) Z`, $d$
  of `fubiniStudyPrimitive n`, with `fubiniStudyLift_def` and
  `fubiniStudyLift_apply`:
  $\rho_z(v,w)=\dfrac{\omega_0(v,w)}{\lvert z\rvert^2}-\dfrac{\langle z,v\rangle\,\omega_0(z,w)-\langle z,w\rangle\,\omega_0(z,v)}{\lvert z\rvert^4}$,
  $\langle z,v\rangle=\operatorname{Re}\sum_i\bar z_iv_i$; `isClosed_fubiniStudyLift`.
- `fubiniStudyLift_eq_del_delBar`: the complexification of
  `fubiniStudyLift n` is `(Complex.I / 2) • J_Z.del (J_Z.delBar f)` for
  $f=\log\lvert z\rvert^2$, by `Potential.lean` and
  `nijenhuis_ofComplexManifold`.
- `sphereStdForm n : TauCeti.SmoothTwoForm (𝓡 (2 * n + 1)) (sphere (0 :
  StdSpace (Fin (n + 1))) 1)`, the pull-back of
  `(stdForm (Fin (n + 1))).constSmooth` along the inclusion, with
  `sphereStdForm_apply`, `sphereStdForm_eq_mextDeriv` ($d$ of Tau Ceti's
  `sphereContactForm`) and `isClosed_sphereStdForm`.
- `mpullback_radialProjection_sphereStdForm`:
  `mpullback (radialProjection n) _ (sphereStdForm n) = fubiniStudyLift n`.
- the rotation `stdRotation ι t : StdSpace ι ≃ₗᵢ[ℝ] StdSpace ι`,
  $z\mapsto\cos t\,z+\sin t\,J_0z$, with `stdRotation_apply` and
  `stdForm_stdRotation`, is placed with `stdForm` in
  `LinearAlgebra/Symplectic/Standard/Basic.lean` of *Standard model*; this
  file acts on the sphere by its restriction, Tau Ceti's
  `LinearIsometryEquiv.unitSphereEquiv`.
- `isBasic_sphereStdForm` and `ker_sphereStdForm`: $\sigma$ is basic for
  `sphereHopf n`, and its kernel at every point is that of the derivative
  of `sphereHopf n`.
- `fubiniStudyForm n : TauCeti.SmoothTwoForm 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ))`,
  the descent of `sphereStdForm n` along `sphereHopf n`, with
  `mpullback_sphereHopf_fubiniStudyForm`, `isSymplectic_fubiniStudyForm`,
  `mpullback_mkNonzero_fubiniStudyForm : mpullback (mkNonzero ℂ n) _
  (fubiniStudyForm n) = fubiniStudyLift n`,
  `eval₂_fubiniStudyForm_mfderiv_mkNonzero` (the value on images of tangent
  vectors is $\rho$), and the two uniqueness statements
  `existsUnique_mpullback_mkNonzero_eq` and
  `existsUnique_mpullback_sphereHopf_eq` (part 2).

### `LinearAlgebra/Matrix/DotProduct.lean`

General matrix facts that `Kahler.lean` uses, in namespace `Matrix`:
`mulVec_injective_of_mul_eq_one` (a matrix with a left inverse acts
injectively on vectors, beside Mathlib's `Matrix.mulVec_injective_of_isUnit`)
and `star_mulVec_dotProduct_mulVec` (a matrix with `Aᴴ * A = 1` preserves
`star z ⬝ᵥ v`).

### `Geometry/Manifold/Projectivization/FubiniStudy/Kahler.lean`

- `mpullback_map_fubiniStudyForm (A : Matrix (Fin (n + 1)) (Fin (m + 1)) ℂ)
  (hA : Aᴴ * A = 1)`: the pull-back of `fubiniStudyForm n` along
  `Projectivization.map (Matrix.toLin' A) _` is `fubiniStudyForm m`
  (the injectivity of `Matrix.toLin' A` from `hA`; the implementer looks for
  it in Mathlib first).
- `mpullback_unitary_fubiniStudyForm (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ)`:
  invariance under `Projectivization.mapDiffeomorph
  (Matrix.UnitaryGroup.toLinearEquiv U) ∞` (part 4, first sentence).
- `compatible_fubiniStudyForm : (fubiniStudyForm n).Compatible J_P`, upstairs:
  `mkNonzero` is holomorphic, $\rho$ is $J_0$-invariant, and
  $\rho(v,iv)>0$ for $v\notin\mathbb Cz$ (the kernel of `ker_mfderiv_mkNonzero`).
- `isKahler_fubiniStudyForm : (fubiniStudyForm n).IsKahler J_P`, with
  `nijenhuis_ofComplexManifold` (part 3, first two sentences).
- `mpullback_affineChart_symm_fubiniStudyForm (j : Fin (n + 1))`: along the
  inverse affine chart $w\mapsto[\texttt{Fin.insertNth } j\ 1\ w]$, the
  pull-back is `(4 : ℝ)⁻¹ • d (J.covectorComplexStructure (d f_j))` with
  $f_j(w)=\log(1+\sum_k\lVert w_k\rVert^2)$ (`fubiniStudyAffinePotential n`,
  the same for every $j$), which is
  $\log(\lvert z\rvert^2/\lvert z_j\rvert^2)$ in homogeneous coordinates;
  and `mpullback_affineChart_symm_fubiniStudyForm_eq_del_delBar`, its
  $\tfrac i2\partial\bar\partial f_j$ form (part 3, local potentials).
- `isKahler_mpullback_fubiniStudyForm`: for a complex submanifold
  $f:N\to\mathbb CP^n$ (a `TauCeti.SmoothEmbedding` whose tangent images
  are `J_P`-invariant), the pull-back of `fubiniStudyForm n` is Kähler, and
  symplectic, for the restricted structure of *Complex submanifolds*; it
  applies that part's transfer of `IsKahler` and of symplecticity to
  `isKahler_fubiniStudyForm`. This is the only declaration that waits for
  *Complex submanifolds*.

### `Geometry/Manifold/Projectivization/FubiniStudy/Normalization.lean`

- `eval₂_fubiniStudyForm_affineParam`: on $\mathbb CP^1$, the pull-back along
  `ProjectiveLine.affineParam 0` at $t$ evaluates on $v,w$ as
  $\operatorname{Im}(\bar vw)/(1+\lVert t\rVert^2)^2$ (part 4, affine formula).
- `mpullback_diffeomorphProjectivization_fubiniStudyForm`:
  the pull-back along `OnePoint.diffeomorphProjectivization ℂ ∞` (read on
  the real structures) is `Real.pi • OnePoint.fubiniStudyForm`.
- `sphereToProjectiveLine : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₘ^ω⟮𝓡 2,
  𝓘(ℝ, Fin 1 → ℂ)⟯ ℙ ℂ (Fin 2 → ℂ)`, the composite
  `(OnePoint.diffeomorphSphere v ι).symm.trans
  ((OnePoint.diffeomorphProjectivization ℂ ω).restrictScalars ℝ)` with `v`
  and `ι` as above, with `sphereToProjectiveLine_of_ne_southPole`
  ($[1+x_3:x_1+ix_2]$), `sphereToProjectiveLine_of_ne_northPole`
  ($[x_1-ix_2:1-x_3]$),
  `isOrientationPreservingAt_sphereToProjectiveLine` (for
  `o₃.sphereOrientation` and `oCP1`), and
  `mpullback_sphereToProjectiveLine_fubiniStudyForm` (part 4, stereographic
  sentence), from `OnePoint.inner_mfderiv_diffeomorphSphere` and
  `mpullback_diffeomorphProjectivization_fubiniStudyForm`.
- `integralTopForm_fubiniStudyForm_one : integralTopForm oCP1
  (fubiniStudyForm 1).val = Real.pi`.
- `integralTopForm_mpullback_map_fubiniStudyForm (f) (hf : Injective f)`:
  every line has area `Real.pi` (part 4, last sentence).

Reference for the area form of the sphere: Lee, *Introduction to Smooth
Manifolds*, 2nd ed., Chapters 15–16, as Tau Ceti's `UnitSphere.lean` cites.

### `Geometry/Manifold/Projectivization/FubiniStudy/Darboux.lean`

- `fubiniStudyDarbouxChart n (j : Fin (n + 1)) : PartialDiffeomorph
  𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, StdSpace (Fin n)) (ℙ ℂ (Fin (n + 1) → ℂ))
  (StdSpace (Fin n)) ∞`, with `fubiniStudyDarbouxChart_source`
  (`affineOpen j`), `fubiniStudyDarbouxChart_target` (`Metric.ball 0 1`),
  `fubiniStudyDarbouxChart_mk` ($[v]\mapsto\hat{}\bigl(\tfrac{\lvert v_j\rvert}{\lvert v\rvert}\,(v_{j.\mathrm{succAbove}\,k}/v_j)_k\bigr)$,
  through `complexToRealEuclidean (Fin n)`) and
  `fubiniStudyDarbouxChart_symm_apply`
  ($\zeta\mapsto[\texttt{Fin.insertNth } j\ \sqrt{1-\lVert\zeta\rVert^2}\ \check\zeta]$).
  The inverse is `sphereHopf n` after the section
  $\zeta\mapsto(\check\zeta,\sqrt{1-\lVert\zeta\rVert^2})$ of the sphere,
  whose last coordinate is real, so it pulls `sphereStdForm` back to
  `stdForm`.
- `eval₂_fubiniStudyForm_eq_stdForm_mvfderiv_darbouxChart`: for `x` in the
  source and tangent vectors `v w`,
  `(fubiniStudyForm n).eval₂ x v w = stdForm _ (mvfderiv _ ψ x v) (mvfderiv _ ψ x w)`
  (part 5).
- `exists_darbouxChart_compl_hyperplane (ℓ : Module.Dual ℂ (Fin (n + 1) → ℂ))
  (hℓ : ℓ ≠ 0)`: a chart of the same kind with source
  `{x | ℓ x.rep ≠ 0}` and target the unit ball, from the case of
  coordinate hyperplanes and `mpullback_unitary_fubiniStudyForm` (part 5,
  last sentence).

### `Geometry/Manifold/Projectivization/FubiniStudy/Lagrangian.lean`

- `isLagrangianEmbedding_mapProjective_ofReal`: `mapProjective
  Complex.ofRealHom : ℙ ℝ (Fin (n + 1) → ℝ) → ℙ ℂ (Fin (n + 1) → ℂ)` is a
  Lagrangian embedding for `fubiniStudyForm n`, with the model
  `𝓘(ℝ, Fin n → ℝ)`; its smoothness and immersion property
  (`isSmoothEmbedding_mapProjective_ofReal`) read it in the affine charts as
  the inclusion of the real points, and it is isotropic because $\rho$
  vanishes on real $z,v,w$ (`mkNonzero` over `ℝ` is a submersion by
  `Hopf.lean`).
- `cliffordTorus n : (Fin n → AddCircle (2 * Real.pi)) → ℙ ℂ (Fin (n + 1) → ℂ)`,
  with `cliffordTorus_apply`, `range_cliffordTorus` (the points with
  representatives of equal moduli), `isSmoothEmbedding_cliffordTorus` and
  `isLagrangianEmbedding_cliffordTorus` (part 6). Isotropy holds upstairs:
  at $z=(1,e^{i\theta})$ the tangent vectors $(0,ia_ke^{i\theta_k})_k$ have
  $\omega_0=0$ and $\langle z,\cdot\rangle=0$.
- `fubiniStudyForm_spec`: the conjunction of parts 1–6, with the milestone
  line.

## What the part uses from other parts

- *Standard model* (merged): `StdSpace`, `stdForm`, `stdComplexStructure`,
  `stdForm_def`, `stdForm_apply_eq_inner`, `x_complexToRealEuclidean`,
  `y_complexToRealEuclidean`, and the scoped instance
  `fact_finrank_stdSpace_fin_succ`, which issue H adds to that part's
  file.
- *Complex submanifolds* (issue #864, `Geometry/Symplectic/Manifold/AlmostComplex/Submanifold.lean`):
  only for `isKahler_mpullback_fubiniStudyForm`, through its restricted
  structure and its transfer of `IsKahler` and symplecticity.

Mathlib and Tau Ceti were searched, at the pinned versions, for a smooth or
submersive Hopf map, a Fubini–Study form on $\mathbb CP^n$ for $n\ge2$, a
form on $\mathbb C^{n+1}\setminus0$ of this kind, the identity between
$\tfrac i2\partial\bar\partial f$ and $\tfrac14 d(J^*df)$, an integral of a
form over $\mathbb CP^1$, Darboux charts of $\mathbb CP^n$, and Lagrangian
$\mathbb RP^n$ or Clifford tori; neither has them. Mathlib's
`Matrix.unitaryGroup` and `UnitaryGroup.toLinearEquiv`, and the Tau Ceti
declarations listed above, are used as they are.

## Building issues

In this order; each is blocked by the ones listed, and all are sub-issues of
#870 (*Build the part Complex projective space*). Sizes are estimates.

| # | Issue | Files | Blocked by | Size |
|---|---|---|---|---|
| P | Kähler potentials: $\tfrac i2\partial\bar\partial f=\tfrac14 d(J^*df)$ for $N_J=0$ | `Geometry/Manifold/DifferentialForm/Dolbeault/Potential.lean` | — | 150 |
| H | The Hopf maps as smooth submersions | `Geometry/Manifold/Projectivization/Hopf.lean` | — | 350 |
| B1 | $\alpha_{\mathrm{FS}}$, $\rho_{\mathrm{FS}}$ and the restricted form on the sphere | `FubiniStudy/Basic.lean` (up to `mpullback_radialProjection_sphereStdForm`) | P, H | 300 |
| B2 | The descended form and its uniqueness | `FubiniStudy/Basic.lean` (from `isBasic_sphereStdForm`) | B1 | 250 |
| K1 | Unitary invariance, compatibility, the Kähler property and the local potentials | `FubiniStudy/Kahler.lean` (all but `isKahler_mpullback_fubiniStudyForm`) | B2 | 350 |
| K2 | Complex submanifolds of $\mathbb CP^n$ | `FubiniStudy/Kahler.lean` (`isKahler_mpullback_fubiniStudyForm`) | K1, #864 | 80 |
| N1 | The affine formula, the comparison with `OnePoint.fubiniStudyForm`, and the stereographic map as a composite of Tau Ceti's diffeomorphisms, with its two formulas and its pull-back of the form | `FubiniStudy/Normalization.lean` (up to `mpullback_sphereToProjectiveLine_fubiniStudyForm`) | B2 | 300 |
| N2 | The area of a line | `FubiniStudy/Normalization.lean` (the two integrals) | N1, K1 | 250 |
| D | The Darboux charts | `FubiniStudy/Darboux.lean` | B2, K1 | 300 |
| L | Lagrangian embeddings of real projective space and of the Clifford torus | `FubiniStudy/Lagrangian.lean` (all but `fubiniStudyForm_spec`) | B2 | 300 |
| S | The milestone as one theorem | `FubiniStudy/Lagrangian.lean` (`fubiniStudyForm_spec`) | K1, N2, D, L | 60 |

P and H can start at once. K2 waits for *Complex submanifolds* (#864). The
milestones are proved in S (*Fubini–Study form on complex projective
space*) and K2 (the last sentence of *Complex submanifolds of Kähler
manifolds*).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Example 4.3.3, p. 168, Exercises 4.3.4(i)–(iv) and 4.3.5(i), p. 169.
* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §§1–2 (affine charts; the Fubini–Study form).
* D. Huybrechts, *Complex Geometry: An Introduction*, Universitext,
  Springer, 2005, §§1.3 and 3.1 (Dolbeault operators, $d^c$, Kähler
  potentials), as Tau Ceti's Dolbeault files cite.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in
  Mathematics 218, Springer, 2013, Chapters 15–16 (orientation of the
  sphere, integration), as Tau Ceti's `UnitSphere.lean` cites.
