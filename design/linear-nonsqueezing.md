# Linear nonsqueezing

This is the detailed design of part 7 of `DESIGN.md`, *Linear nonsqueezing*.
It covers the milestones *Affine nonsqueezing theorem*, *Simultaneous normal
form of a symplectic form and an inner product*, *Linear symplectic width of an
ellipsoid* and *Linear symplectic rigidity* of
`atlas/linear-symplectic-geometry.md`, which follow McDuff–Salamon
[McDuffSalamon2017], §2.4 (Theorems 2.4.1, 2.4.2, 2.4.4 and 2.4.8, Lemmas 2.4.5
and 2.4.6, Exercise 2.4.3 and the formula for the volume of an ellipsoid on
p. 60). Williamson's theorem itself is Tau Ceti's; its docstrings cite
Williamson (1936) and Arnold's *Mathematical Methods of Classical Mechanics*,
Appendix 6.

All names below are in the namespace `SymplecticGeometry` unless they are
written with another one. Paths of new files are under `SymplecticGeometry/`;
Tau Ceti paths are relative to `.lake/packages/TauCeti/TauCeti/`, as in
`DESIGN.md`. `ι` is a `Fintype`, and `n` is `Fintype.card ι`. A statement that
needs `DecidableEq ι` takes it as an extra hypothesis, as the diagonal-matrix
results of `Ellipsoid/Basic.lean` do.

## Decisions

`DESIGN.md` leaves three questions to this file.

- **Value type of the width.** `linearSymplecticWidth A : ℝ≥0∞`. A set that
  contains no ball has width `0` (the supremum of the empty family), and a set
  that contains balls of every radius, such as the whole space, has width `∞`.
  Tau Ceti's capacities (`Geometry/Symplectic/Capacity/`) also take values in
  `ℝ≥0∞`. The radii in the supremum range over `ℝ≥0`, since
  `Metric.closedBall 0 r` is empty for `r < 0` and would otherwise contribute
  `π r²`.
- **How an ellipsoid centred at `0` is given.** By a positive definite
  quadratic form: the ellipsoid of `Q : QuadraticForm ℝ V` with `Q.PosDef` is
  the set `{v | Q v ≤ 1}`. The library does not name this set; statements
  write it out, so that nothing wraps `setOf`. This is the form that Tau Ceti's
  Williamson theorem takes as input
  (`TauCeti.SymplecticForm.exists_isDarbouxBasis_eq_sum_smul_elliptic_of_posDef`
  needs `Q.PosDef`), and it determines `Q`
  (`QuadraticMap.PosDef.eq_of_setOfPred_le_one_eq` below), so invariants of the
  set may be defined through `Q`. The other description, the image of the
  closed unit ball under a linear isomorphism (the form of Tau Ceti's
  `Analysis/InnerProductSpace/JohnEllipsoid.lean`), is related to this one by
  two lemmas, in both directions.
- **"Symplectic or anti-symplectic".** For a linear map
  `Ψ : StdSpace ι →ₗ[ℝ] StdSpace ι`, the statement is the disjunction of the
  pointwise identities

  ```lean
  (∀ z w, stdForm ι (Ψ z) (Ψ w) = stdForm ι z w) ∨
    ∀ z w, stdForm ι (Ψ z) (Ψ w) = -stdForm ι z w
  ```

  that is, $\Psi^*\omega_0=\pm\omega_0$. It is pointwise because `Ψ` is a
  linear map and not an equivalence (Tau Ceti's `IsSymplectomorphism` takes an
  equivalence), and because the rigidity theorem starts from a linear map. No
  new predicate is defined for it. Either identity forces `Ψ` to be injective,
  hence an equivalence
  (`TauCeti.SymplecticForm.bijective_of_forall_apply_eq_or_forall_apply_eq_neg` below). The anti-symplectic
  maps are the compositions of symplectic ones with the reflection `stdConj ι`
  ($y\mapsto -y$), which is how their properties are proved.

Further choices of this design:

- **Linear symplectic maps of the model.** A linear symplectic map of
  `StdSpace ι` is an `e : StdSpace ι ≃ₗ[ℝ] StdSpace ι` with
  `IsSymplectomorphism (stdForm ι) (stdForm ι) e`, Tau Ceti's predicate. The
  dictionary of *Standard model*, `mem_symplecticGroup_iff_isSymplectomorphism`,
  translates to `Matrix.symplecticGroup ι ℝ`; the milestone *Affine
  nonsqueezing theorem* is stated with a matrix as well, as the book states it.
- **Balls and cylinders are closed.** $B^{2n}(r)$ is
  `Metric.closedBall (0 : StdSpace ι) r`, with the Euclidean norm of all $2n$
  coordinates (see `DESIGN.md`, *Euclidean model*). The cylinder over the disc
  of radius $R$ in the $(x_i,y_i)$-plane is `stdCylinder i R`. The coordinate
  index `i : ι` is a parameter, since a general `ι` has no first element;
  permuting the coordinate pairs is symplectic, so nothing depends on `i`.
  The cylinder is defined with a square root, so that it is empty for `R < 0`;
  with `R²` it would not be, and the affine nonsqueezing theorem would fail
  for negative `R`. The theorems for balls need `0 ≤ r`, since a ball of
  negative radius is empty.
- **Affine symplectic maps.** $\mathrm{ASp}$ is a subgroup of Mathlib's group
  `V ≃ᵃ[ℝ] V` of affine equivalences, for every real symplectic vector space
  `(V, ω)`: those whose linear part `AffineEquiv.linear` is a symplectomorphism.
  It is the preimage, under Mathlib's `AffineEquiv.linearHom`, of Tau Ceti's
  group of linear symplectomorphisms
  `LinearMap.BilinForm.isometryGroup ω.toBilinForm`
  (`LinearAlgebra/BilinearForm/Isometry.lean`), so no subgroup of linear
  symplectomorphisms is added beside it, `Matrix.symplecticGroup` and
  `TauCeti.GLSymplectic` (`DESIGN.md`, *One representation per notion*).
- **Symplectic spectrum.** `symplecticSpectrum Q` is a `Multiset ℝ` of
  cardinality `n`. A multiset needs no order on `ι`, and the book's ordering
  $r_1\le\dots\le r_n$ only serves to say which radius is the smallest; the
  width theorem takes the smallest one as a hypothesis on an element of the
  multiset. For `ι = Fin n` the sorted version is a corollary.
- **Dimension zero.** For `ι` empty, `StdSpace ι` is a point. Every nonempty
  set then has width `∞`, the spectrum is empty, there are no cylinders, and
  every linear map is both symplectic and anti-symplectic. The theorems below
  hold there as stated, without a `Nonempty ι` hypothesis, with two
  exceptions: the width of an ellipsoid is stated for a radius in the
  spectrum, which exists only if `ι` is nonempty, and
  `linearSymplecticWidth_image_closedBall` takes `[Nonempty ι]`, since in
  dimension zero a ball is a point, of width `∞`.

## Files and their contents

The part owns the folder `Analysis/InnerProductSpace/Symplectic/`, as
`DESIGN.md` says; `Ellipsoid.lean` and `LinearWidth.lean` of `DESIGN.md` are
split into folders, as `AGENTS.md` allows. The supporting results that do not
need the standard model sit with their topics: the injectivity of maps that
pull a symplectic form back to plus or minus itself, two lemmas on positive
definite forms, the two descriptions of ellipsoids in an inner product space,
a lemma on bilinear maps that agree up to sign, the transport of Hamiltonian
endomorphisms, and Williamson's orthogonal Darboux bases and the uniqueness
of his frequencies. Those about Tau Ceti's notions are in files with the paths
of the Tau Ceti files they extend, so that they can join them. No folder below
has the name of a Tau Ceti file at the same place.

| File | Contents | Issue |
|---|---|---|
| `Geometry/Symplectic/SymplecticTransport.lean` | maps with $\Psi^*\omega=\pm\omega$ are bijective | 1 |
| `Analysis/InnerProductSpace/Symplectic/AffineSymplectic.lean` | $\mathrm{ASp}$, cylinders, `stdConj`, adjoints | 1 |
| `Analysis/InnerProductSpace/Symplectic/Nonsqueezing.lean` | affine nonsqueezing | 2 |
| `LinearAlgebra/QuadraticForm/PosDef.lean` | a positive definite form is determined by its sublevel set `≤ 1`; images of that set | 3 |
| `Analysis/InnerProductSpace/Ellipsoid.lean` | sublevel sets of positive definite forms are the linear images of balls | 3 |
| `Analysis/InnerProductSpace/Symplectic/Ellipsoid/Basic.lean` | `stdEllipsoidForm`, `stdEllipsoid` | 3 |
| `Analysis/InnerProductSpace/Symplectic/Ellipsoid/NormalForm.lean` | normal form of ellipsoids | 3 |
| `Geometry/Symplectic/Hamiltonian/Quadratic.lean` | Hamiltonian endomorphisms under symplectomorphisms | 4 |
| `Geometry/Symplectic/Hamiltonian/Williamson.lean` | orthogonal Darboux bases, uniqueness of Williamson's frequencies | 4 |
| `Analysis/InnerProductSpace/Symplectic/Ellipsoid/Spectrum.lean` | `symplecticSpectrum`, its uniqueness, the volume, the milestone | 5 |
| `Analysis/InnerProductSpace/Symplectic/LinearWidth/Basic.lean` | `linearSymplecticWidth` and its axioms | 6 |
| `Analysis/InnerProductSpace/Symplectic/LinearWidth/Ellipsoid.lean` | the width of an ellipsoid, the milestone | 7 |
| `LinearAlgebra/BilinearMap/Sign.lean` | functionals and bilinear maps equal up to sign | 8 |
| `Analysis/InnerProductSpace/Symplectic/Rigidity.lean` | `HasLinearNonsqueezing`, affine rigidity, the milestone | 8 |

### `Geometry/Symplectic/SymplecticTransport.lean`

In Tau Ceti's namespace `TauCeti.SymplecticForm`, for `V` a real module of
finite dimension and `ω : TauCeti.SymplecticForm V`:

- `bijective_of_forall_apply_eq_or_forall_apply_eq_neg`: a linear map
  `Ψ : V →ₗ[ℝ] V` with
  `(∀ v w, ω (Ψ v) (Ψ w) = ω v w) ∨ ∀ v w, ω (Ψ v) (Ψ w) = -ω v w` is
  bijective. Either identity makes `Ψ` an isometry from `ω.toBilinForm` to
  `ω.toBilinForm` or to `-ω.toBilinForm`, so Tau Ceti's
  `LinearMap.BilinForm.Isometry.injective` (with `ω.separatingLeft`) shows
  it injective, and Mathlib's `LinearMap.injective_iff_surjective` bijective
  in finite dimension; `LinearEquiv.ofBijective` makes it an equivalence.
  The case of `stdForm ι` is an application, not a separate lemma.

### `AffineSymplectic.lean`

For `V` a real module and `ω : TauCeti.SymplecticForm V`:

- `affineSymplecticGroup ω : Subgroup (V ≃ᵃ[ℝ] V) :=
  (LinearMap.BilinForm.isometryGroup ω.toBilinForm).comap AffineEquiv.linearHom`,
  so that closure comes from Tau Ceti's group.
  API: `mem_affineSymplecticGroup_iff` (`@[simp]`,
  `f ∈ affineSymplecticGroup ω ↔ IsSymplectomorphism ω ω f.linear`, from
  `Subgroup.mem_comap`, Tau Ceti's `@[simp] mem_isometryGroup_iff` and
  `isSymplectomorphism_iff`);
  `AffineEquiv.constVAdd_mem_affineSymplecticGroup` (translations);
  `LinearEquiv.toAffineEquiv_mem_affineSymplecticGroup_iff` (a linear
  equivalence is in it if and only if it is a symplectomorphism);
  `mem_affineSymplecticGroup_iff_exists`: `f` is in it if and only if
  `⇑f = fun v ↦ e v + v₀` for a symplectomorphism `e` and a `v₀` (namely
  `e = f.linear`, `v₀ = f 0`).
- `mem_affineSymplecticGroup_stdForm_iff_matrix`: for `StdSpace ι`,
  `f ∈ affineSymplecticGroup (stdForm ι)` if and only if there are
  `A ∈ Matrix.symplecticGroup ι ℝ` and `z₀` with
  `⇑f = fun z ↦ Matrix.toEuclideanLin A z + z₀`, by the dictionary of
  *Standard model*.

For `StdSpace ι`:

- `stdCylinder (i : ι) (R : ℝ) : Set (StdSpace ι) :=
  {z | √(z.x i ^ 2 + z.y i ^ 2) ≤ R}`, with `stdCylinder_def`,
  `mem_stdCylinder_iff_of_nonneg` (`0 ≤ R → (z ∈ stdCylinder i R ↔
  z.x i ^ 2 + z.y i ^ 2 ≤ R ^ 2)`), `stdCylinder_eq_empty` for `R < 0`,
  `closedBall_subset_stdCylinder` (`closedBall 0 R ⊆ stdCylinder i R`) and
  `stdCylinder_mono`.
- `stdConj ι : StdSpace ι ≃ₗᵢ[ℝ] StdSpace ι`, the reflection
  $(x,y)\mapsto(x,-y)$, complex conjugation under `complexToRealEuclidean ι`.
  API: `@[simp] stdConj_x`, `@[simp] stdConj_y`, `stdConj_symm`
  (`(stdConj ι).symm = stdConj ι`), `@[simp] stdConj_stdConj`,
  `stdForm_stdConj` (`stdForm ι (stdConj ι z) (stdConj ι w) =
  -stdForm ι z w`), `stdConj_image_closedBall`, `stdConj_image_stdCylinder`,
  and `det_stdConj` (`LinearMap.det = (-1) ^ n`). Search Tau Ceti for a
  conjugation of `EuclideanSpace ℝ (ι ⊕ ι)` before defining it; if one
  exists, use it instead.
- The anti-symplectic maps, for an equivalence `Ψ` with `hΨ : ∀ z w,
  stdForm ι (Ψ z) (Ψ w) = -stdForm ι z w`, writing `stdConj ι` for its
  underlying linear equivalence:
  `isSymplectomorphism_trans_stdConj_of_forall_apply_eq_neg`
  (`Ψ.trans (stdConj ι)` is a symplectomorphism),
  `isSymplectomorphism_stdConj_trans_of_forall_apply_eq_neg`
  (`(stdConj ι).trans Ψ` is one) and `det_eq_neg_one_pow_of_forall_apply_eq_neg`
  (`LinearMap.det Ψ = (-1) ^ n`, Exercise 2.4.3, first half, from Tau Ceti's
  `TauCeti.SymplecticForm.IsSymplectomorphism.det_eq_one` and `det_stdConj`).
- `TauCeti.SymplecticForm.IsSymplectomorphism.adjoint`: for a
  symplectomorphism `e` of `stdForm ι`, the adjoint
  `ContinuousLinearEquiv.adjointEquiv e.toContinuousLinearEquiv` (Tau Ceti's
  `Analysis/InnerProductSpace/Adjoint.lean`), as a linear equivalence, is a
  symplectomorphism. This is the transpose of a symplectic matrix, Mathlib's
  `SymplecticGroup.transpose_mem`, through the dictionary and Mathlib's
  `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`.

### `Nonsqueezing.lean`

```lean
/-- Affine nonsqueezing, for an affine symplectic map. -/
theorem le_of_image_closedBall_subset_stdCylinder
    {f : StdSpace ι ≃ᵃ[ℝ] StdSpace ι} (hf : f ∈ affineSymplecticGroup (stdForm ι))
    {i : ι} {r R : ℝ} (hr : 0 ≤ r) (h : f '' Metric.closedBall 0 r ⊆ stdCylinder i R) :
    r ≤ R

/-- Milestone: *Affine nonsqueezing theorem*. -/
theorem le_of_mem_symplecticGroup_of_image_closedBall_subset_stdCylinder
    {A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ}
    (hA : A ∈ Matrix.symplecticGroup ι ℝ) (z₀ : StdSpace ι) {i : ι} {r R : ℝ}
    (hr : 0 ≤ r)
    (h : (fun z ↦ Matrix.toEuclideanLin A z + z₀) '' Metric.closedBall 0 r ⊆
      stdCylinder i R) :
    r ≤ R
```

The atlas states the theorem for radii without saying that they are
nonnegative; `0 ≤ r` is the convention made explicit, and needs no entry in
`ERRATA.md` (without it, the empty ball lies in every cylinder). The proof is
the book's, with the slip that the atlas notes corrected: for `u` and `v` the
images of the unit vectors in the $x_i$ and $y_i$ directions under the
adjoint of the linear part, $\omega_0(u,v)=1$
(`TauCeti.SymplecticForm.IsSymplectomorphism.adjoint`)
and $\lvert\omega_0(u,v)\rvert\le\lvert u\rvert\lvert v\rvert$
(`stdForm_apply_eq_inner` and Cauchy–Schwarz), so one of them, say `u`, has
norm at least `1`; then for one of the two points $\pm r\,u/\lvert u\rvert$
of the ball, whatever the translation, the $x_i$-coordinate of its image has
absolute value at least $r$, so the image lies in no cylinder of radius less
than $r$. Expected size: 150 lines.

### `Ellipsoid/Basic.lean`

- `stdEllipsoidForm (r : ι → ℝ) : QuadraticForm ℝ (StdSpace ι)`, the form
  $\sum_j (x_j^2+y_j^2)/r_j^2$, built from Mathlib's
  `QuadraticMap.weightedSumSquares` (weights `(r j)⁻¹ ^ 2` on `inl j` and
  `inr j`) composed with the coordinate equivalence of `EuclideanSpace`, with
  `stdEllipsoidForm_def` and `@[simp] stdEllipsoidForm_apply` in terms of
  `z.x` and `z.y`; `stdEllipsoidForm_posDef` (if no `r j` is `0`), from Tau
  Ceti's `EuclideanSpace.posDef_iff_of_forall_eq_sum_mul_sq` with the weights
  `(r j)⁻¹ ^ 2` on `inl j` and `inr j`.
- `stdEllipsoid (r : ι → ℝ) : Set (StdSpace ι) := {z | stdEllipsoidForm r z ≤ 1}`,
  the book's $E(r)$, with `stdEllipsoid_def`, `@[simp] mem_stdEllipsoid_iff`,
  `closedBall_subset_stdEllipsoid` (`hmin : ∀ j, r i ≤ r j` gives
  `closedBall 0 (r i) ⊆ stdEllipsoid r`; no sign is needed, since for
  `r i < 0` the ball is empty and for `r i = 0` it is `{0}`). The matching
  inclusion in a cylinder is in issue 7, so that this issue does not wait for
  issue 1.
- `stdEllipsoid_eq_image_closedBall`: for `r` with nonzero entries
  (`hr : ∀ j, r j ≠ 0`),
  `stdEllipsoid r` is the image of `closedBall 0 1` under the diagonal map
  $(x_j,y_j)\mapsto(r_jx_j,r_jy_j)$, whose determinant is $\prod_j r_j^2$.

### `LinearAlgebra/QuadraticForm/PosDef.lean`

Next to Tau Ceti's `QuadraticMap.PosDef.comp`, for quadratic forms on any
real module:

- `QuadraticMap.PosDef.eq_of_setOfPred_le_one_eq`: for `hQ : Q.PosDef` and any
  `Q'`, `{v | Q v ≤ 1} = {v | Q' v ≤ 1}` implies `Q = Q'`. Only `Q` needs to
  be positive definite: if `Q' v ≤ 0` for some `v ≠ 0`, the whole line
  through `v` lies in `{v | Q' v ≤ 1}`, on which `Q` is bounded, while
  `Q (t • v) = t ^ 2 * Q v` is not. So `Q'` is positive away from `0`, and
  homogeneity concludes.
- `QuadraticMap.image_setOfPred_le_one`: for a linear equivalence `e`,
  `e '' {v | Q v ≤ 1} = {v | Q.comp e.symm v ≤ 1}`; that `Q.comp e.symm` is
  positive definite with `Q` is Tau Ceti's `QuadraticMap.PosDef.comp`.

### `Analysis/InnerProductSpace/Ellipsoid.lean`

In a real inner product space of finite dimension, with no symplectic
structure:

- `LinearEquiv.exists_posDef_image_closedBall_eq`: the image of
  `closedBall 0 r` (`0 < r`) under a linear equivalence `e` is
  `{v | Q v ≤ 1}` for a positive definite `Q`
  ($Q(v)=\lVert e^{-1}v\rVert^2/r^2$). This makes symplectic balls ellipsoids,
  which issue 8 uses.
- `QuadraticMap.PosDef.exists_linearEquiv_image_closedBall_eq`, the
  converse: for `Q.PosDef`, `{v | Q v ≤ 1}` is the image of `closedBall 0 1`
  under a linear equivalence. Tau Ceti's
  `TauCeti.nonempty_isometryEquiv_toQuadraticForm'_one_of_posDef` gives an
  isometry from `Q` to the sum of squares on `Fin (finrank ℝ V) → ℝ`;
  composed with the Euclidean coordinates of an orthonormal basis
  (`stdOrthonormalBasis`), it carries `Q` to `‖·‖ ^ 2`, whose sublevel set
  `≤ 1` is `closedBall 0 1`.

### `Ellipsoid/NormalForm.lean`

```lean
/-- The normal form of an ellipsoid centred at `0`. -/
theorem exists_isSymplectomorphism_image_eq_stdEllipsoid
    {Q : QuadraticForm ℝ (StdSpace ι)} (hQ : Q.PosDef) :
    ∃ (r : ι → ℝ) (e : StdSpace ι ≃ₗ[ℝ] StdSpace ι), (∀ j, 0 < r j) ∧
      IsSymplectomorphism (stdForm ι) (stdForm ι) e ∧
      e '' {z | Q z ≤ 1} = stdEllipsoid r
```

The file uses `stdDarbouxBasisOf (τ : Fin m ≃ ι) : Module.Basis
(Fin m × Fin 2) ℝ (StdSpace ι)`, which is in *Standard model*'s
`Standard/Basic.lean`: Tau Ceti's `stdDarbouxBasis m` carried to
`StdSpace ι` by the product comparison of *Standard model* and the relabelling
`τ`, with `stdDarbouxBasisOf_def`, the `@[simp]` basis-vector lemmas
`stdDarbouxBasisOf_zero` and `_one` (`EuclideanSpace.single (Sum.inl (τ k)) 1`
and `EuclideanSpace.single (Sum.inr (τ k)) 1`, under `[DecidableEq ι]`), the
`@[simp]` coordinate lemmas
`stdDarbouxBasisOf_repr_zero` and `_one` (`x_{τ k}` and `y_{τ k}`),
and `isDarbouxBasis_stdDarbouxBasisOf`. It proves
`stdEllipsoidForm_eq_sum_smul_elliptic`: `stdEllipsoidForm r = ∑ k, (2 /
r (τ k) ^ 2) • elliptic (stdDarbouxBasisOf τ) k`. Both this file and
`Ellipsoid/Spectrum.lean` use the basis.

The normal form applies Williamson's theorem to `Q`, which gives a Darboux
basis `b` and frequencies `ν`, takes $r_k=\sqrt{2/\nu_k}$ and a relabelling
`σ : Fin m ≃ ι` (`m = n` by dimension), and takes for `e` the map sending `b`
to `stdDarbouxBasisOf σ`, through the two coordinate equivalences
`Module.Basis.darbouxBasisEquiv` of Tau Ceti; the formula above gives
`stdEllipsoidForm r ∘ e = Q`. The basis uses the public lemma
`isSymplectomorphism_piLpCongrLeft_sumCongr`: for `σ : ι ≃ κ`, relabelling
the coordinate pairs, `(LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
(σ.sumCongr σ)).toLinearEquiv`, is a symplectomorphism from `stdForm ι` to
`stdForm κ`, which is in *Standard model*'s `Standard/Basic.lean`. Expected
size of issue 3, its four files together: 350 lines.

### `Geometry/Symplectic/Hamiltonian/Quadratic.lean`

In Tau Ceti's namespace `TauCeti.SymplecticForm`, so that it can join Tau
Ceti's file of the same name:

- `IsSymplectomorphism.hamiltonianEnd_comp`, beside Tau Ceti's
  `IsSymplectomorphism.hamiltonianVectorField_comp`: for
  `he : IsSymplectomorphism ω₁ ω₂ e` (explicit, so that
  `he.hamiltonianEnd_comp Q` works),
  `ω₁.hamiltonianEnd (Q.comp e) = e.symm ∘ₗ ω₂.hamiltonianEnd Q ∘ₗ e`, from
  Tau Ceti's `eq_hamiltonianEnd_iff` (the defining identity
  `ω (A_Q v) w = polar Q v w`) or from
  `IsSymplectomorphism.hamiltonianVectorField_comp` (`Transport.lean`).
  Nothing in the library uses it since `exists_perm_eq_of_image_stdEllipsoid_eq`
  took another route (see `Ellipsoid/Spectrum.lean`); it stays as API, the
  counterpart for Hamiltonian endomorphisms of Tau Ceti's lemma for vector
  fields.

### `Geometry/Symplectic/Hamiltonian/Williamson.lean`

In Tau Ceti's namespace `TauCeti.SymplecticForm`, so that it can join Tau
Ceti's file of the same name:

- `exists_isDarbouxBasis_orthogonal`, a Darboux basis that is orthogonal for
  an inner product:

  ```lean
  /-- A Darboux basis that is orthogonal for the ambient inner product, with
  `‖q_k‖ = ‖p_k‖`; `q_k = b (k, 0)` and `p_k = b (k, 1)` as in Tau Ceti's
  `IsDarbouxBasis`. -/
  theorem TauCeti.SymplecticForm.exists_isDarbouxBasis_orthogonal
      {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      (ω : TauCeti.SymplecticForm V) :
      ∃ (m : ℕ) (b : Module.Basis (Fin m × Fin 2) ℝ V), ω.IsDarbouxBasis b ∧
        (Pairwise fun k l ↦ ⟪b k, b l⟫_ℝ = 0) ∧ ∀ k, ‖b (k, 0)‖ = ‖b (k, 1)‖
  ```

  It is Williamson's theorem for the quadratic form `‖v‖²` (or
  `‖v‖² / 2`): the polar form of `∑ ν_k • elliptic b k` vanishes on distinct
  basis vectors and equals `ν_k` on `q_k` and on `p_k` (Tau Ceti's
  `polar_elliptic`).
- `IsDarbouxBasis.exists_perm_eq_of_sum_smul_elliptic_eq`: if
  `∑ k, ν k • elliptic b k = ∑ k, μ k • elliptic c k` for Darboux bases `b`,
  `c` and positive `ν`, `μ`, then `∃ σ : Equiv.Perm (Fin m), μ = ν ∘ σ`.
  Proof: by `IsDarbouxBasis.hamiltonianEnd_sum_smul_elliptic_apply_fst` and
  `_snd`, the square of the Hamiltonian endomorphism is $-\nu_k^2$ on the
  plane of `b (k, 0)`, `b (k, 1)`; so for `t > 0` the kernel of
  `A_Q ^ 2 + t ^ 2` has dimension twice the number of `k` with `ν k = t`, in
  either basis, and equal counts give the permutation. The positivity of the
  frequencies is what makes `ν k ^ 2` determine `ν k`.

Expected size of issue 4, both files: 300 lines.

### `Ellipsoid/Spectrum.lean`

- `exists_perm_eq_of_image_stdEllipsoid_eq`: for positive `r`, `r'` and a symplectomorphism `e`,
  `e '' stdEllipsoid r = stdEllipsoid r'` implies `∃ σ : Equiv.Perm ι,
  r' = r ∘ σ`. By `eq_of_setOfPred_le_one_eq`, `stdEllipsoidForm r ∘ e⁻¹ =
  stdEllipsoidForm r'`. With `d = stdDarbouxBasisOf τ` for `τ : Fin n ≃ ι`,
  `stdEllipsoidForm_eq_sum_smul_elliptic` writes the left side as
  `∑ k, (2 / r (τ k) ^ 2) • elliptic (d.map e) k` and the right side as
  `∑ k, (2 / r' (τ k) ^ 2) • elliptic d k`; `d.map e` is a Darboux basis
  (Tau Ceti's `IsDarbouxBasis.map`), so the uniqueness of issue 4 gives the
  permutation of the frequencies $2/r_j^2$, hence of the radii. Its corollary
  for `ι = Fin m` and monotone `r`, `r'` is `r = r'`.
- `symplecticSpectrum (Q : QuadraticForm ℝ (StdSpace ι)) : Multiset ℝ`: the
  multiset `Finset.univ.val.map r` for the `r` that
  `exists_isSymplectomorphism_image_eq_stdEllipsoid` gives when `Q.PosDef`,
  chosen by `Classical.choose`, and `0` otherwise. API:
  `symplecticSpectrum_eq` (the characterization: for `Q.PosDef`, positive `r`
  and a symplectomorphism `e` with `e '' {z | Q z ≤ 1} = stdEllipsoid r`, the
  spectrum is `Finset.univ.val.map r`; it makes the choice irrelevant),
  `card_symplecticSpectrum` (`= n` for `Q.PosDef`), `posDef_of_mem_symplecticSpectrum`,
  `pos_of_mem_symplecticSpectrum`,
  `symplecticSpectrum_comp` (invariance under `Q ↦ Q.comp e` for a
  symplectomorphism `e`) and `@[simp] symplecticSpectrum_stdEllipsoidForm`
  (`= Finset.univ.val.map r` for positive `r`).
- `volume_setOfPred_le_one`: for `Q.PosDef`,
  `volume {z | Q z ≤ 1} = ENNReal.ofReal (π ^ n / n ! *
  ((symplecticSpectrum Q).map (· ^ 2)).prod)`, from
  `IsSymplectomorphism.det_eq_one`, Mathlib's
  `MeasureTheory.Measure.addHaar_image_linearMap`,
  `stdEllipsoid_eq_image_closedBall` and
  `InnerProductSpace.volume_closedBall_of_dim_even`. For `n = 0` both sides
  are `1`.
- The milestone, one theorem with the atlas's two contexts:

  ```lean
  /-- Milestone: *Simultaneous normal form of a symplectic form and an inner product*. -/
  theorem exists_isDarbouxBasis_orthogonal_and_stdEllipsoid_normalForm
      (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      (ω : TauCeti.SymplecticForm V) (ι : Type*) [Fintype ι] :
      (∃ (m : ℕ) (b : Module.Basis (Fin m × Fin 2) ℝ V), ω.IsDarbouxBasis b ∧
        (Pairwise fun k l ↦ ⟪b k, b l⟫_ℝ = 0) ∧ ∀ k, ‖b (k, 0)‖ = ‖b (k, 1)‖) ∧
      ∀ Q : QuadraticForm ℝ (StdSpace ι), Q.PosDef →
        (∃ (r : ι → ℝ) (e : StdSpace ι ≃ₗ[ℝ] StdSpace ι), (∀ j, 0 < r j) ∧
          IsSymplectomorphism (stdForm ι) (stdForm ι) e ∧
          e '' {z | Q z ≤ 1} = stdEllipsoid r) ∧
        (∀ (r : ι → ℝ) (e : StdSpace ι ≃ₗ[ℝ] StdSpace ι), (∀ j, 0 < r j) →
          IsSymplectomorphism (stdForm ι) (stdForm ι) e →
          e '' {z | Q z ≤ 1} = stdEllipsoid r →
          symplecticSpectrum Q = Finset.univ.val.map r) ∧
        MeasureTheory.volume {z | Q z ≤ 1} = ENNReal.ofReal
          (π ^ Fintype.card ι / (Fintype.card ι).factorial *
            ((symplecticSpectrum Q).map (· ^ 2)).prod)
  ```

  It is assembled from the results above; `DESIGN.md` asks for a single
  theorem for this milestone, since Tau Ceti proves its first part.

Expected size: 300 lines.

### `LinearWidth/Basic.lean`

```lean
/-- The linear symplectic width: the supremum of `π r²` over the radii `r` of
the balls whose image under some affine symplectic map lies in `A`. -/
noncomputable def linearSymplecticWidth (A : Set (StdSpace ι)) : ℝ≥0∞ :=
  ⨆ (r : ℝ≥0) (f ∈ affineSymplecticGroup (stdForm ι))
    (_ : f '' Metric.closedBall 0 r ⊆ A), ENNReal.ofReal (π * r ^ 2)
```

API, with the book's properties of $w_L$ (p. 56) as theorems:

- `linearSymplecticWidth_def`, `le_linearSymplecticWidth` (a ball of radius
  `r ≥ 0` whose image lies in `A` gives `π r² ≤ w`),
  `linearSymplecticWidth_le_iff` (`w ≤ c` if and only if every such ball has
  `π r² ≤ c`), `@[simp] linearSymplecticWidth_empty` (`= 0`),
  `@[simp] linearSymplecticWidth_univ` (`= ∞`).
- `linearSymplecticWidth_mono` (monotone in `A`).
- `linearSymplecticWidth_image` (invariance: `w (f '' A) = w A` for
  `f ∈ affineSymplecticGroup (stdForm ι)`), and
  `linearSymplecticWidth_image_of_forall_apply_eq_or_forall_apply_eq_neg`: `w (Ψ '' A) = w A` for a linear
  map with $\Psi^*\omega_0=\pm\omega_0$ (Exercise 2.4.3, second half, through
  `stdConj`).
- `linearSymplecticWidth_smul` (conformality): for `c ≠ 0`,
  `w (c • A) = ENNReal.ofReal (c ^ 2) * w A`; the conjugate of an affine
  symplectic map by $z\mapsto cz$ is affine symplectic. For `c = 0` it fails
  in dimension zero, where `{0}` has width `∞`.
- `linearSymplecticWidth_image_closedBall`: for `[Nonempty ι]`, `0 ≤ r` and
  `f` affine symplectic, `w (f '' closedBall z r) = ENNReal.ofReal (π * r ^ 2)`.
  The upper bound comes from `closedBall_subset_stdCylinder` and the next
  item. In dimension zero the ball is a point and its width is `∞`.
- `linearSymplecticWidth_image_stdCylinder`: `w (f '' stdCylinder i R) =
  ENNReal.ofReal (π * R ^ 2)` for `0 ≤ R`, by
  `le_of_image_closedBall_subset_stdCylinder`; `0` for `R < 0`.

Expected size: 300 lines.

### `LinearWidth/Ellipsoid.lean`

- `stdEllipsoid_subset_stdCylinder`: `stdEllipsoid r ⊆ stdCylinder i (r i)`
  for `0 < r i`.
- `linearSymplecticWidth_stdEllipsoid`: for positive `r` and `i` with
  `∀ j, r i ≤ r j`, `w (stdEllipsoid r) = ENNReal.ofReal (π * r i ^ 2)`, from
  `closedBall_subset_stdEllipsoid` and `stdEllipsoid_subset_stdCylinder`.
- The milestone:

  ```lean
  /-- Milestone: *Linear symplectic width of an ellipsoid*. -/
  theorem linearSymplecticWidth_setOfPred_le_one {Q : QuadraticForm ℝ (StdSpace ι)}
      {s : ℝ} (hs : s ∈ symplecticSpectrum Q)
      (hmin : ∀ t ∈ symplecticSpectrum Q, s ≤ t) :
      let E := {z | Q z ≤ 1}
      linearSymplecticWidth E = ENNReal.ofReal (π * s ^ 2) ∧
      linearSymplecticWidth E =
        ⨆ (f ∈ affineSymplecticGroup (stdForm ι)) (r : ℝ≥0)
          (_ : f '' Metric.closedBall 0 r ⊆ E),
          linearSymplecticWidth (f '' Metric.closedBall 0 r) ∧
      linearSymplecticWidth E =
        ⨅ (f ∈ affineSymplecticGroup (stdForm ι)) (i : ι) (R : ℝ)
          (_ : E ⊆ f '' stdCylinder i R),
          linearSymplecticWidth (f '' stdCylinder i R)
  ```

  The middle and last equalities are the book's supremum over symplectic
  balls in `E` and infimum over symplectic cylinders containing `E`. The `let`
  may be replaced by writing the set out, if that elaborates better.

Expected size: 200 lines.

### `LinearAlgebra/BilinearMap/Sign.lean`

Over any field `K`, with no finite dimension and no nondegeneracy:

- `LinearMap.eq_or_eq_neg_of_forall_sq_eq_sq`, after Mathlib's
  `eq_or_eq_neg_of_sq_eq_sq`: for `f g : M →ₗ[K] K` with
  `∀ x, f x ^ 2 = g x ^ 2`, `f = g ∨ f = -g`. If `f` and `g` are linearly
  independent, some `x` has `f x = 1` and `g x = 0`; otherwise `g = c • f` and
  `c ^ 2 = 1`.
- `LinearMap.eq_or_eq_neg_of_forall_sq_eq_sq₂`: the same for
  `B ω : M →ₗ[K] M →ₗ[K] K` with `∀ x y, B x y ^ 2 = ω x y ^ 2`: each
  `B x` is `± ω x`, and the sign is the same for all `x` with `ω x ≠ 0`,
  by comparing `x`, `x'` and `x + x'`.

Search Mathlib for both first. Expected size: 100 lines.

### `Rigidity.lean`

- The linear nonsqueezing property, with the atlas's quantifiers: images of
  balls and cylinders under linear symplectic maps.

  ```lean
  def HasLinearNonsqueezing (Ψ : StdSpace ι →ₗ[ℝ] StdSpace ι) : Prop :=
    ∀ (φ θ : StdSpace ι ≃ₗ[ℝ] StdSpace ι),
      IsSymplectomorphism (stdForm ι) (stdForm ι) φ →
      IsSymplectomorphism (stdForm ι) (stdForm ι) θ →
      ∀ (i : ι) (r R : ℝ), 0 ≤ r →
        Ψ '' (φ '' Metric.closedBall 0 r) ⊆ θ '' stdCylinder i R → r ≤ R
  ```

  with `hasLinearNonsqueezing_iff` (the body) and the examples
  `TauCeti.SymplecticForm.IsSymplectomorphism.hasLinearNonsqueezing` (affine
  nonsqueezing) and
  `hasLinearNonsqueezing_of_forall_apply_eq_or_forall_apply_eq_neg` (for $\Psi^*\omega_0=\pm\omega_0$).
  Translates of balls and cylinders would give the same property, since the
  sets are convex and centrally symmetric; the design follows the atlas.
- Affine rigidity (Theorem 2.4.2):

  ```lean
  theorem forall_apply_eq_or_forall_apply_eq_neg_of_hasLinearNonsqueezing
      (Ψ : StdSpace ι ≃ₗ[ℝ] StdSpace ι) (h : HasLinearNonsqueezing (Ψ : StdSpace ι →ₗ[ℝ] _))
      (h' : HasLinearNonsqueezing (Ψ.symm : StdSpace ι →ₗ[ℝ] _)) :
      (∀ z w, stdForm ι (Ψ z) (Ψ w) = stdForm ι z w) ∨
        ∀ z w, stdForm ι (Ψ z) (Ψ w) = -stdForm ι z w
  ```

  and the equivalence `hasLinearNonsqueezing_and_hasLinearNonsqueezing_symm_iff`
  (`HasLinearNonsqueezing Ψ ∧ HasLinearNonsqueezing Ψ.symm` if and only if
  the same disjunction), whose right-to-left direction is
  `hasLinearNonsqueezing_of_forall_apply_eq_or_forall_apply_eq_neg` for `Ψ` and for `Ψ.symm`. Route, which
  may be replaced by the book's: a symplectic cylinder `θ '' stdCylinder i R`
  is $\{z:\langle a,z\rangle^2+\langle b,z\rangle^2\le R^2\}$ for the images
  `a`, `b` of the coordinate vectors under the adjoint of `θ⁻¹`, which have
  $\omega_0(a,b)=1$, and every such pair arises (Tau Ceti's
  `TauCeti.SymplecticForm.exists_isSymplectomorphism_apply_eq`). With
  $\alpha=\Psi^Ta$ and $\beta=\Psi^Tb$, a symplectic map $\varphi$ moves the
  pair $(\alpha,\beta)$ so that the largest eigenvalue of its Gram matrix is
  as close to $\lvert\omega_0(\alpha,\beta)\rvert$ as wanted: by
  `exists_isSymplectomorphism_apply_eq` if $\omega_0(\alpha,\beta)\ne0$, and
  if it is `0` by Tau Ceti's Witt extension theorem
  (`exists_isSymplectomorphism_extend`) into the subspace `{z | z.y = 0}`,
  followed by the symplectic scaling $(x,y)\mapsto(\varepsilon x,
  y/\varepsilon)$. So the property for `Ψ` gives
  $\lvert\omega_0(\Psi^Ta,\Psi^Tb)\rvert\ge\lvert\omega_0(a,b)\rvert$ for all
  `a`, `b`, the property for `Ψ⁻¹` the reverse inequality, and
  `LinearMap.eq_or_eq_neg_of_forall_sq_eq_sq₂` turns the equality into
  $(\Psi^T)^*\omega_0=\pm\omega_0$, hence the same for `Ψ`.
- The milestone:

  ```lean
  /-- Milestone: *Linear symplectic rigidity*. -/
  theorem forall_linearSymplecticWidth_image_eq_iff (Ψ : StdSpace ι →ₗ[ℝ] StdSpace ι) :
      (∀ Q : QuadraticForm ℝ (StdSpace ι), Q.PosDef →
        linearSymplecticWidth (Ψ '' {z | Q z ≤ 1}) =
          linearSymplecticWidth {z | Q z ≤ 1}) ↔
      (∀ z w, stdForm ι (Ψ z) (Ψ w) = stdForm ι z w) ∨
        ∀ z w, stdForm ι (Ψ z) (Ψ w) = -stdForm ι z w
  ```

  From right to left: `linearSymplecticWidth_image_of_forall_apply_eq_or_forall_apply_eq_neg`. From left to
  right: if `Ψ` is not injective and `ι` is nonempty, the image of the unit
  ball lies in a proper subspace, which contains no ball of positive radius
  and so has width `0`, while the ball has width `π`; so `Ψ` is an
  equivalence. Its inverse also preserves the widths of ellipsoids, since
  `Ψ` maps ellipsoids onto ellipsoids (`QuadraticMap.image_setOfPred_le_one`). A
  symplectic ball is an ellipsoid
  (`LinearEquiv.exists_posDef_image_closedBall_eq`) of width
  `π r²`, and a symplectic cylinder has width `π R²`
  (`linearSymplecticWidth_image_stdCylinder`), so both `Ψ` and `Ψ⁻¹` have the
  linear nonsqueezing property, and affine rigidity concludes. For `ι` empty
  both sides hold.

Expected size: 450 lines, with `Sign.lean`.

## What the part uses

- *Standard model* (#7, #8): `StdSpace`, `StdSpace.x`, `StdSpace.y`,
  `stdForm` with `stdForm_apply` and `stdForm_apply_eq_inner`, the product
  comparison `isSymplectomorphism_sumEquivProd` (as named in #41), the
  relabelling of coordinate pairs `isSymplectomorphism_piLpCongrLeft_sumCongr`,
  and `mem_symplecticGroup_iff_isSymplectomorphism`.
- Tau Ceti: `TauCeti.SymplecticForm`, `IsSymplectomorphism` with
  `isSymplectomorphism_iff`, `IsSymplectomorphism.det_eq_one`,
  `LinearMap.BilinForm.isometryGroup` with `mem_isometryGroup_iff`,
  `LinearMap.BilinForm.Isometry.injective`, `QuadraticMap.PosDef.comp`,
  `EuclideanSpace.posDef_iff_of_forall_eq_sum_mul_sq`,
  `TauCeti.nonempty_isometryEquiv_toQuadraticForm'_one_of_posDef`,
  `ContinuousLinearEquiv.adjointEquiv`, `IsDarbouxBasis` with
  `IsDarbouxBasis.map`, `stdDarbouxBasis` with `isDarbouxBasis_stdDarbouxBasis`,
  `Module.Basis.darbouxBasisEquiv` with
  `Module.Basis.darbouxBasisEquiv_fst_apply`, `_snd_apply` and
  `IsDarbouxBasis.isSymplectomorphism_darbouxBasisEquiv`, `elliptic` with
  `elliptic_apply` and `polar_elliptic`, `hamiltonianEnd` with
  `IsDarbouxBasis.hamiltonianEnd_sum_smul_elliptic_apply_fst` and `_snd`,
  `eq_hamiltonianEnd_iff`, `IsSymplectomorphism.hamiltonianVectorField_comp`,
  Williamson's theorem
  `exists_isDarbouxBasis_eq_sum_smul_elliptic_of_posDef`, Witt's theorem
  `exists_isSymplectomorphism_extend` and
  `exists_isSymplectomorphism_apply_eq`.
- Mathlib: `AffineEquiv` with `linear`, `linearHom`, `constVAdd`;
  `Subgroup.comap`; `Metric.closedBall`; `QuadraticMap.PosDef`,
  `QuadraticMap.weightedSumSquares`, `LinearMap.injective_iff_surjective`,
  `stdOrthonormalBasis`;
  `LinearIsometryEquiv.piLpCongrLeft`;
  `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`;
  `Matrix.symplecticGroup`, `SymplecticGroup.transpose_mem`;
  `MeasureTheory.Measure.addHaar_image_linearMap`,
  `InnerProductSpace.volume_closedBall_of_dim_even`.

Mathlib and Tau Ceti were searched, at the pinned versions, for the notions
this part defines (affine symplectic maps, cylinders, ellipsoids, symplectic
spectra, linear widths, the nonsqueezing property); neither has them. Tau
Ceti's capacities are the nonlinear Hofer–Zehnder ones, and its
`JohnEllipsoid.lean` describes ellipsoids as images of balls without naming
them.

## Building issues

In this order; each is blocked by the ones listed, and all are sub-issues of
#3 (through #31, *Build the part Linear nonsqueezing*). Sizes are estimates.

| # | Issue | Files | Blocked by | Size |
|---|---|---|---|---|
| 1 | Affine symplectic maps, cylinders and the reflection of `StdSpace` | `Geometry/Symplectic/SymplecticTransport.lean`, `AffineSymplectic.lean` | #7, #8 | 250 |
| 2 | The affine nonsqueezing theorem | `Nonsqueezing.lean` | 1 | 150 |
| 3 | Ellipsoids and their normal form | `LinearAlgebra/QuadraticForm/PosDef.lean`, `Analysis/InnerProductSpace/Ellipsoid.lean`, `Ellipsoid/Basic.lean`, `Ellipsoid/NormalForm.lean` | #7 | 350 |
| 4 | Orthogonal Darboux bases and the uniqueness of the frequencies in Williamson's theorem | `Geometry/Symplectic/Hamiltonian/Quadratic.lean`, `Geometry/Symplectic/Hamiltonian/Williamson.lean` | — | 300 |
| 5 | The symplectic spectrum of an ellipsoid and its volume | `Ellipsoid/Spectrum.lean` | 3, 4 | 300 |
| 6 | The linear symplectic width | `LinearWidth/Basic.lean` | 1, 2 | 300 |
| 7 | The width of an ellipsoid | `LinearWidth/Ellipsoid.lean` | 3, 5, 6 | 200 |
| 8 | Linear symplectic rigidity | `LinearAlgebra/BilinearMap/Sign.lean`, `Rigidity.lean` | 1, 2, 3, 6 | 450 |

Issues 1 and 3 can start as soon as *Standard model* is merged, and issue 4
at once. The milestones are proved in issues 2
(*Affine nonsqueezing theorem*), 5 (*Simultaneous normal form of a symplectic
form and an inner product*), 7 (*Linear symplectic width of an ellipsoid*)
and 8 (*Linear symplectic rigidity*).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §2.4.
* J. Williamson, *On the algebraic problem concerning the normal forms of
  linear dynamical systems*, American Journal of Mathematics 58 (1936),
  141–163.
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed.,
  Graduate Texts in Mathematics 60, Springer, 1989, Appendix 6.
