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
`DESIGN.md`. `ι` is a `Fintype` with `DecidableEq`, and `n` is `Fintype.card ι`.

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
  (`QuadraticMap.PosDef.setOf_le_one_injective` below), so invariants of the
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
  hence an equivalence (`bijective_of_stdForm_pullback` below). The anti-symplectic
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
  Its membership is stated through `IsSymplectomorphism`, so no subgroup of
  linear symplectomorphisms is added beside `Matrix.symplecticGroup` and
  `TauCeti.GLSymplectic` (`DESIGN.md`, *One representation per notion*).
- **Symplectic spectrum.** `symplecticSpectrum Q` is a `Multiset ℝ` of
  cardinality `n`. A multiset needs no order on `ι`, and the book's ordering
  $r_1\le\dots\le r_n$ only serves to say which radius is the smallest; the
  width theorem takes the smallest one as a hypothesis on an element of the
  multiset. For `ι = Fin n` the sorted version is a corollary.
- **Dimension zero.** For `ι` empty, `StdSpace ι` is a point. Every nonempty
  set then has width `∞`, the spectrum is empty, there are no cylinders, and
  every linear map is both symplectic and anti-symplectic. The theorems below
  hold there as stated, without a `Nonempty ι` hypothesis, except that the
  width of an ellipsoid is stated for a radius in the spectrum, which exists
  only if `ι` is nonempty.

## Files and their contents

The part owns the folder `Analysis/InnerProductSpace/Symplectic/`, as
`DESIGN.md` says; `Ellipsoid.lean` and `LinearWidth.lean` of `DESIGN.md` are
split into folders, as `AGENTS.md` allows. Two supporting files sit with their
topics: a lemma on bilinear maps that agree up to sign, and the uniqueness of
Williamson's frequencies, which is a statement about Tau Ceti's notions. No
folder below has the name of a Tau Ceti file at the same place.

| File | Contents | Issue |
|---|---|---|
| `Analysis/InnerProductSpace/Symplectic/AffineSymplectic.lean` | $\mathrm{ASp}$, cylinders, `stdConj`, adjoints | 1 |
| `Analysis/InnerProductSpace/Symplectic/Nonsqueezing.lean` | affine nonsqueezing | 2 |
| `Analysis/InnerProductSpace/Symplectic/Ellipsoid/Basic.lean` | `stdEllipsoidForm`, `stdEllipsoid`, ellipsoids and images of balls | 3 |
| `Analysis/InnerProductSpace/Symplectic/Ellipsoid/NormalForm.lean` | simultaneous normal form, normal form of ellipsoids | 3 |
| `Geometry/Symplectic/Hamiltonian/Williamson.lean` | uniqueness of Williamson's frequencies | 4 |
| `Analysis/InnerProductSpace/Symplectic/Ellipsoid/Spectrum.lean` | `symplecticSpectrum`, its uniqueness, the volume, the milestone | 5 |
| `Analysis/InnerProductSpace/Symplectic/LinearWidth/Basic.lean` | `linearSymplecticWidth` and its axioms | 6 |
| `Analysis/InnerProductSpace/Symplectic/LinearWidth/Ellipsoid.lean` | the width of an ellipsoid, the milestone | 7 |
| `LinearAlgebra/BilinearMap/Sign.lean` | functionals and bilinear maps equal up to sign | 8 |
| `Analysis/InnerProductSpace/Symplectic/Rigidity.lean` | `HasLinearNonsqueezing`, affine rigidity, the milestone | 8 |

### `AffineSymplectic.lean`

For `V` a real module and `ω : TauCeti.SymplecticForm V`:

- `affineSymplecticGroup ω : Subgroup (V ≃ᵃ[ℝ] V)`, with carrier
  `{f | IsSymplectomorphism ω ω f.linear}`; closure from
  `IsSymplectomorphism.refl`, `.trans`, `.symm` and `AffineEquiv.linearHom`.
  API: `mem_affineSymplecticGroup_iff` (`@[simp]`, the carrier);
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
- `bijective_of_stdForm_pullback`: a linear map `Ψ` of `StdSpace ι` with
  $\Psi^*\omega_0=\pm\omega_0$ (the disjunction of *Decisions*) is injective,
  by nondegeneracy, so bijective; `LinearEquiv.ofBijective` makes it an
  equivalence.
- The anti-symplectic maps: if `∀ z w, stdForm ι (Ψ z) (Ψ w) =
  -stdForm ι z w` for an equivalence `Ψ`, then `Ψ.trans (stdConj ι)` and
  `(stdConj ι).trans Ψ` are symplectomorphisms, and `LinearMap.det Ψ =
  (-1) ^ n` (Exercise 2.4.3, first half), from Tau Ceti's
  `TauCeti.SymplecticForm.IsSymplectomorphism.det_eq_one`.
- `IsSymplectomorphism.adjoint`: the adjoint of a symplectomorphism `e` of
  `stdForm ι` (`LinearMap.adjoint`, as an equivalence) is a symplectomorphism.
  This is the transpose of a symplectic matrix, Mathlib's
  `SymplecticGroup.transpose_mem` through the dictionary.

### `Nonsqueezing.lean`

```lean
/-- Affine nonsqueezing, for an affine symplectic map. -/
theorem le_of_image_closedBall_subset_stdCylinder
    {f : StdSpace ι ≃ᵃ[ℝ] StdSpace ι} (hf : f ∈ affineSymplecticGroup (stdForm ι))
    {i : ι} {r R : ℝ} (hr : 0 ≤ r) (h : f '' Metric.closedBall 0 r ⊆ stdCylinder i R) :
    r ≤ R

/-- Milestone: *Affine nonsqueezing theorem*. -/
theorem le_of_affine_image_closedBall_subset_stdCylinder {A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ}
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
adjoint of the linear part, $\omega_0(u,v)=1$ (`IsSymplectomorphism.adjoint`)
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
  `z.x` and `z.y`; `stdEllipsoidForm_posDef` (if no `r j` is `0`).
- `stdEllipsoid (r : ι → ℝ) : Set (StdSpace ι) := {z | stdEllipsoidForm r z ≤ 1}`,
  the book's $E(r)$, with `stdEllipsoid_def`, `mem_stdEllipsoid_iff`,
  `closedBall_subset_stdEllipsoid` (`0 < r j` for all `j` and `r i ≤ r j` for
  all `j` give `closedBall 0 (r i) ⊆ stdEllipsoid r`). The matching
  inclusion in a cylinder is in issue 7, so that this issue does not wait for
  issue 1.
- `stdEllipsoid_eq_image_closedBall`: for `r` with positive entries,
  `stdEllipsoid r` is the image of `closedBall 0 1` under the diagonal map
  $(x_j,y_j)\mapsto(r_jx_j,r_jy_j)$, whose determinant is $\prod_j r_j^2$.
- `QuadraticMap.PosDef.setOf_le_one_injective` (in Mathlib's namespace, for
  any real module): two positive definite forms with the same set
  `{v | Q v ≤ 1}` are equal, by homogeneity.
- `image_setOf_le_one`: for a linear equivalence `e`,
  `e '' {v | Q v ≤ 1} = {v | Q.comp e.symm v ≤ 1}`, and `Q.comp e.symm` is
  positive definite with `Q` (Mathlib may have the second; search
  `QuadraticMap.PosDef` first).
- `exists_posDef_image_closedBall_eq`: in a real inner product space of
  finite dimension, the image of `closedBall 0 r` (`0 < r`) under a linear
  equivalence is `{v | Q v ≤ 1}` for a positive definite `Q`
  ($Q(v)=\lVert e^{-1}v\rVert^2/r^2$). This makes symplectic balls ellipsoids,
  which issue 8 uses.

### `Ellipsoid/NormalForm.lean`

```lean
/-- A Darboux basis that is orthogonal for the ambient inner product, with
`‖q_k‖ = ‖p_k‖`; `q_k = b (k, 0)` and `p_k = b (k, 1)` as in Tau Ceti's
`IsDarbouxBasis`. -/
theorem TauCeti.SymplecticForm.exists_isDarbouxBasis_orthogonal
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (ω : TauCeti.SymplecticForm V) :
    ∃ (m : ℕ) (b : Module.Basis (Fin m × Fin 2) ℝ V), ω.IsDarbouxBasis b ∧
      (Pairwise fun k l ↦ ⟪b k, b l⟫_ℝ = 0) ∧ ∀ k, ‖b (k, 0)‖ = ‖b (k, 1)‖

/-- The normal form of an ellipsoid centred at `0`. -/
theorem exists_isSymplectomorphism_image_eq_stdEllipsoid
    {Q : QuadraticForm ℝ (StdSpace ι)} (hQ : Q.PosDef) :
    ∃ (r : ι → ℝ) (e : StdSpace ι ≃ₗ[ℝ] StdSpace ι), (∀ j, 0 < r j) ∧
      IsSymplectomorphism (stdForm ι) (stdForm ι) e ∧
      e '' {z | Q z ≤ 1} = stdEllipsoid r
```

The first is Williamson's theorem for the quadratic form `‖v‖²` (or
`‖v‖² / 2`): the polar form of `∑ ν_k • elliptic b k` vanishes on distinct
basis vectors and equals `ν_k` on `q_k` and on `p_k` (Tau Ceti's
`polar_elliptic`). The second applies Williamson's theorem to `Q`, takes
$r_k=\sqrt{2/\nu_k}$, and builds `e` from Tau Ceti's
`Module.Basis.darbouxBasisEquiv`, the product comparison of *Standard model*,
and a reindexing `Fin m ≃ ι` (`m = n` by dimension). If that reindexing needs
the lemma that relabelling the coordinate pairs of `StdSpace` is a
symplectomorphism, that lemma is public and in this file. The file also gives
the converse of `exists_posDef_image_closedBall_eq`: every `{z | Q z ≤ 1}`
with `Q.PosDef` is the image of `closedBall 0 1` under a linear equivalence.
Expected size of `Ellipsoid/`, issue 3: 350 lines.

### `Geometry/Symplectic/Hamiltonian/Williamson.lean`

In Tau Ceti's namespace `TauCeti.SymplecticForm`, so that it can join Tau
Ceti's file of the same name:

- `hamiltonianEnd_comp`: for a symplectomorphism `e` from `ω₁` to `ω₂`,
  `ω₁.hamiltonianEnd (Q.comp e) = e.symm ∘ₗ ω₂.hamiltonianEnd Q ∘ₗ e`, from
  the defining identity `ω (A_Q v) w = polar Q v w`. Search Tau Ceti's
  `Geometry/Symplectic/Hamiltonian/Quadratic.lean` and `Transport.lean`
  first.
- `IsDarbouxBasis.exists_equiv_eq_of_sum_smul_elliptic_eq`: if
  `∑ k, ν k • elliptic b k = ∑ k, μ k • elliptic c k` for Darboux bases `b`,
  `c` and positive `ν`, `μ`, then `μ = ν ∘ σ` for an `Equiv.Perm (Fin m)`.
  Proof: by `IsDarbouxBasis.hamiltonianEnd_sum_smul_elliptic_apply_fst` and
  `_snd`, the square of the Hamiltonian endomorphism is $-\nu_k^2$ on the
  plane of `b (k, 0)`, `b (k, 1)`; so for `t > 0` the kernel of
  `A_Q ^ 2 + t ^ 2` has dimension twice the number of `k` with `ν k = t`, in
  either basis, and equal counts give the permutation. The positivity of the
  frequencies is what makes `ν k ^ 2` determine `ν k`.

Expected size: 250 lines.

### `Ellipsoid/Spectrum.lean`

- `exists_perm_eq_of_image_stdEllipsoid_eq`: for positive `r`, `r'` and a symplectomorphism `e`,
  `e '' stdEllipsoid r = stdEllipsoid r'` implies `∃ σ : Equiv.Perm ι,
  r' = r ∘ σ`, from `setOf_le_one_injective`, `hamiltonianEnd_comp` and the
  uniqueness of issue 4 (the elliptic blocks of the standard Darboux basis of
  `StdSpace ι` are $(x_j^2+y_j^2)/2$, with $\nu_j=2/r_j^2$). Its corollary
  for `ι = Fin m` and monotone `r`, `r'` is `r = r'`.
- `symplecticSpectrum (Q : QuadraticForm ℝ (StdSpace ι)) : Multiset ℝ`: the
  multiset `Finset.univ.val.map r` for the `r` that
  `exists_isSymplectomorphism_image_eq_stdEllipsoid` gives when `Q.PosDef`,
  chosen by `Classical.choose`, and `0` otherwise. API:
  `symplecticSpectrum_eq` (the characterization: for `Q.PosDef`, positive `r`
  and a symplectomorphism `e` with `e '' {z | Q z ≤ 1} = stdEllipsoid r`, the
  spectrum is `Finset.univ.val.map r`; it makes the choice irrelevant),
  `card_symplecticSpectrum` (`= n` for `Q.PosDef`), `pos_of_mem_symplecticSpectrum`,
  `symplecticSpectrum_comp` (invariance under `Q ↦ Q.comp e` for a
  symplectomorphism `e`) and `symplecticSpectrum_stdEllipsoidForm`.
- `volume_setOf_le_one`: for `Q.PosDef`,
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
      (ω : TauCeti.SymplecticForm V) (ι : Type*) [Fintype ι] [DecidableEq ι] :
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
  `π r² ≤ c`), `linearSymplecticWidth_empty`, `linearSymplecticWidth_univ`
  (`= ∞`).
- `linearSymplecticWidth_mono` (monotone in `A`).
- `linearSymplecticWidth_image` (invariance: `w (f '' A) = w A` for
  `f ∈ affineSymplecticGroup (stdForm ι)`), and
  `linearSymplecticWidth_image_of_pullback`: `w (Ψ '' A) = w A` for a linear
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
  theorem linearSymplecticWidth_setOf_le_one {Q : QuadraticForm ℝ (StdSpace ι)}
      (hQ : Q.PosDef) {s : ℝ} (hs : s ∈ symplecticSpectrum Q)
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

- `LinearMap.eq_or_eq_neg_of_forall_sq_eq`: for `f g : M →ₗ[K] K` with
  `∀ x, f x ^ 2 = g x ^ 2`, `f = g ∨ f = -g`. If `f` and `g` are linearly
  independent, some `x` has `f x = 1` and `g x = 0`; otherwise `g = c • f` and
  `c ^ 2 = 1`.
- `LinearMap.eq_or_eq_neg_of_forall_sq_eq₂`: the same for
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
  `IsSymplectomorphism.hasLinearNonsqueezing` (affine nonsqueezing) and
  `hasLinearNonsqueezing_of_pullback` (for $\Psi^*\omega_0=\pm\omega_0$).
  Translates of balls and cylinders would give the same property, since the
  sets are convex and centrally symmetric; the design follows the atlas.
- Affine rigidity (Theorem 2.4.2):

  ```lean
  theorem pullback_eq_or_eq_neg_of_hasLinearNonsqueezing
      (Ψ : StdSpace ι ≃ₗ[ℝ] StdSpace ι) (h : HasLinearNonsqueezing (Ψ : StdSpace ι →ₗ[ℝ] _))
      (h' : HasLinearNonsqueezing (Ψ.symm : StdSpace ι →ₗ[ℝ] _)) :
      (∀ z w, stdForm ι (Ψ z) (Ψ w) = stdForm ι z w) ∨
        ∀ z w, stdForm ι (Ψ z) (Ψ w) = -stdForm ι z w
  ```

  with its converse, so that the file states the equivalence. Route, which
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
  `LinearMap.eq_or_eq_neg_of_forall_sq_eq₂` turns the equality into
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

  From right to left: `linearSymplecticWidth_image_of_pullback`. From left to
  right: if `Ψ` is not injective and `ι` is nonempty, the image of the unit
  ball lies in a proper subspace, which contains no ball of positive radius
  and so has width `0`, while the ball has width `π`; so `Ψ` is an
  equivalence. Its inverse also preserves the widths of ellipsoids, since
  `Ψ` maps ellipsoids onto ellipsoids (`image_setOf_le_one`). A symplectic
  ball is an ellipsoid (`exists_posDef_image_closedBall_eq`) of width
  `π r²`, and a symplectic cylinder has width `π R²`
  (`linearSymplecticWidth_image_stdCylinder`), so both `Ψ` and `Ψ⁻¹` have the
  linear nonsqueezing property, and affine rigidity concludes. For `ι` empty
  both sides hold.

Expected size: 450 lines, with `Sign.lean`.

## What the part uses

- *Standard model* (#7, #8): `StdSpace`, `StdSpace.x`, `StdSpace.y`,
  `stdForm` with `stdForm_apply` and `stdForm_apply_eq_inner`, the product
  comparison `isSymplectomorphism_sumEquivProd` (as named in #41), and
  `mem_symplecticGroup_iff_isSymplectomorphism`.
- Tau Ceti: `TauCeti.SymplecticForm`, `IsSymplectomorphism` with `refl`,
  `symm`, `trans`, `IsSymplectomorphism.det_eq_one`, `IsDarbouxBasis`,
  `Module.Basis.darbouxBasisEquiv` with
  `IsDarbouxBasis.isSymplectomorphism_darbouxBasisEquiv`, `elliptic` with
  `elliptic_apply` and `polar_elliptic`, `hamiltonianEnd` with
  `IsDarbouxBasis.hamiltonianEnd_sum_smul_elliptic_apply_fst` and `_snd`,
  Williamson's theorem
  `exists_isDarbouxBasis_eq_sum_smul_elliptic_of_posDef`, Witt's theorem
  `exists_isSymplectomorphism_extend` and
  `exists_isSymplectomorphism_apply_eq`.
- Mathlib: `AffineEquiv` with `linear`, `linearHom`, `constVAdd`;
  `Metric.closedBall`; `QuadraticMap.PosDef`,
  `QuadraticMap.weightedSumSquares`; `LinearMap.adjoint`;
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
| 1 | Affine symplectic maps, cylinders and the reflection of `StdSpace` | `AffineSymplectic.lean` | #7, #8 | 250 |
| 2 | The affine nonsqueezing theorem | `Nonsqueezing.lean` | 1 | 150 |
| 3 | Ellipsoids and the simultaneous normal form | `Ellipsoid/Basic.lean`, `Ellipsoid/NormalForm.lean` | #7 | 350 |
| 4 | Uniqueness of the frequencies in Williamson's theorem | `Geometry/Symplectic/Hamiltonian/Williamson.lean` | — | 250 |
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
