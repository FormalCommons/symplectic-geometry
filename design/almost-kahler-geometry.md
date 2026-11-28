# Almost Kähler geometry

This is the detailed design of part 26 of `DESIGN.md`, *Almost Kähler
geometry*. It proves two milestones of `atlas/almost-complex-structures.md`:
*Levi-Civita derivative of a compatible almost complex structure* and
*Parallel almost complex structures and the Kähler condition*. They follow
McDuff–Salamon [McDuffSalamon2017], Lemma 4.1.14 (equations
(4.1.9)–(4.1.12), by the coordinate-free argument of its first proof) and
Lemma 4.2.5 with its proof (equation (4.2.4)), and Moroianu
[Moroianu2007], Lemma 5.4 and Theorem 5.5, for the equivalence without
the integrability theorem. The fourth identity of the first milestone is
also equation (7) of Apostolov–Drăghici [ApostolovDraghici2003], §3.3.

Paths of new files are under `SymplecticGeometry/`. Tau Ceti paths are
relative to `.lake/packages/TauCeti/TauCeti/` and Mathlib paths to
`.lake/packages/mathlib/Mathlib/`. All declarations of Tau Ceti and
Mathlib named below were checked against the pinned versions, and the
statements of *Main results* were checked to elaborate there, with the
proofs left out. Throughout, `I : ModelWithCorners ℝ E H` with
`[FiniteDimensional ℝ E]` and `[IsManifold I ∞ M]`; boundary is allowed,
since nothing below uses charts. `σ : TauCeti.SmoothTwoForm I M` is the
two-form, called $\omega$ on the page (in Lean, `ω` is notation once
`ContDiff` is open), `J : TauCeti.SmoothAlmostComplexStructure I M`, and
`cov : CovariantDerivative I E (TangentSpace I : M → Type _)` a covariant
derivative on $TM$. In the statements,

- $\nabla_uJ$ at `x` is `cov.hom cov J.toEndomorphism x u`, Tau Ceti's Hom
  connection applied to the section of $J$, as `DESIGN.md` defines $\nabla J$
  for *Nijenhuis tensor*'s `Covariant.lean`; written `D u` below. If that
  file gives the operator a name, the statements use it instead, through
  its defining lemma, and nothing else changes;
- $d\sigma(u,v,w)$ is `TauCeti.mextDeriv σ.val x ![u, v, w]`, the book's $d$
  with no factor (`TauCeti.SmoothForm.mextDeriv_apply_two`, see
  *Almost complex structures, Kähler manifolds and characteristic classes*
  in `DESIGN.md`);
- $N_J$ is Tau Ceti's `J.nijenhuis x`, the book's $N_J$ with no sign.

## What there is, and what is missing

- **Levi-Civita connection** (Mathlib,
  `Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean`):
  `CovariantDerivative.leviCivitaConnection I M` for the metric of a
  `RiemannianBundle (fun x : M ↦ TangentSpace I x)` instance that is
  `IsContMDiffRiemannianBundle I 1`, the predicate
  `CovariantDerivative.IsLeviCivitaConnection` (metric compatible and
  torsion free, for the instance's metric), and
  `isLeviCivitaConnection_leviCivitaConnection`. Tau Ceti's
  `Bundle.ContMDiffRiemannianMetric.inner_eq`
  (`Geometry/Manifold/VectorBundle/Riemannian/Basic.lean`) evaluates the
  inner product of the instance `⟨g.toRiemannianMetric⟩`, and
  `Bundle.ContMDiffRiemannianMetric.isMetricCompatible_iff_inner`
  (`CovariantDerivative/Metric/Basic.lean`) reads metric compatibility for
  that instance through `g.inner`. Tau Ceti installs a metric
  `g : ContMDiffRiemannianMetric` inside statements with
  `letI : RiemannianBundle … := ⟨g.toRiemannianMetric⟩`
  (`Geometry/Calibrated/Basic.lean`).
- **Induced connections** (Tau Ceti,
  `Geometry/Manifold/VectorBundle/CovariantDerivative/`):
  `CovariantDerivative.hom` with `hom_apply` and `hom_hom_apply`
  (`Hom.lean`), the trivial connection `CovariantDerivative.trivial` with
  `trivial_apply` (`Trivial.lean`), torsion (`Torsion.lean`, on Mathlib's
  `CovariantDerivative.torsion`), and
  `CovariantDerivative.IsMetricCompatible.inner_hom_eq_neg`
  (`Metric/Hom.lean`): a metric connection keeps a differentiable field of
  skew-adjoint endomorphisms skew-adjoint after differentiation. That is
  the second identity of the first milestone, once $J$ is known to be
  skew-adjoint for $g_J$.
- **Exterior derivative through a connection.** Tau Ceti's
  `ExteriorDerivative.lean` treats one-forms
  (`CovariantDerivative.mextDeriv_ofSubsingleton`, its torsion-free case
  and the closedness criterion). Its `Exterior/Two.lean` defines exterior
  covariant differentiation of bundle-valued two-forms,
  `exteriorCovariantDerivativeTwo`, with the intrinsic formula
  `exteriorCovariantDerivativeTwo_apply` and independence of the auxiliary
  tangent connection `exteriorCovariantDerivativeTwo_eq`. Its definition is
  the cyclic sum of the covariant derivative of the form plus a torsion
  term, but that expression and its lemmas (`twoFormTensor`,
  `exteriorTwoValue`, `hom_twoFormTensor_apply`) are private, so no public
  statement gives $d\sigma$ as the cyclic sum of $\nabla\sigma$. This is
  what `TwoForm.lean` adds.
- **Two-forms as bilinear fields.** `TauCeti.SmoothTwoForm.flat σ x :
  TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ`, with `flat_apply`
  (`σ.flat x v w = σ.eval₂ x v w`) and `contMDiff_flat`
  (`Geometry/Symplectic/Manifold/Flat.lean`). So $\nabla\sigma$ at `x` is
  `cov.hom (cov.hom (CovariantDerivative.trivial ℝ)) σ.flat x`, and no new
  definition is needed.
- **The metric of a compatible pair.** Tau Ceti's
  `Geometry/Symplectic/Manifold/AlmostComplex/Metric.lean` works with a
  `RiemannianBundle` instance and the hypothesis
  `hJ : ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (J x v)`, and proves
  `TauCeti.SmoothTwoForm.compatible_of_inner_eq` (such a `J` is compatible
  with `σ`). Its steps $g(Ju,w)=\sigma(u,w)$ and $g(Ju,Jw)=g(u,w)$ are the
  public `TauCeti.SmoothAlmostComplexStructure.inner_apply_left_of_inner_eq` and
  `TauCeti.SmoothAlmostComplexStructure.inner_apply_apply_of_inner_eq`.
  Tau Ceti's `CompatibleMetric.lean` has
  `TauCeti.SmoothTwoForm.Compatible.metric`, the metric $g_J$ of a
  compatible pair as a `Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)`,
  with `metric_inner`.
- **Kähler pairs.** `TauCeti.SmoothTwoForm.IsKahler` with `isKahler_iff`
  (closed, compatible, `J.nijenhuis = 0`), and `TauCeti.SmoothForm.IsClosed`
  (`mextDeriv σ.val = 0`).
- **Missing.** Apart from the anticommutation below, none of the identities
  of either milestone is in Mathlib or Tau Ceti (the atlas page's Lean
  correspondence finds none, and a search of the pinned trees for `hom`
  applied to `toEndomorphism`, *almost Kähler* and *nearly Kähler* finds
  only prose in Tau Ceti's Seiberg–Witten files).
  The anticommutation $(\nabla_vJ)J+J(\nabla_vJ)=0$ is Tau Ceti's
  `CovariantDerivative.hom_apply_apply_anticomm`, in pointwise form, with
  the differentiability of `J` from `Covariant.lean`; the formula of $N_J$
  through a torsion-free connection is built by *Nijenhuis tensor*
  (`Nijenhuis.lean`, #863).

## Decisions

`DESIGN.md` leaves two questions to this file.

1. **How $g_J$ is installed.** In two layers.
   - The identities are proved for a `RiemannianBundle` instance on
     $TM$, taken as a variable together with
     `[IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]`
     (which Mathlib's `IsLeviCivitaConnection` needs), the hypothesis
     `hJ : ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (J x v)` of Tau Ceti's
     `AlmostComplex/Metric.lean`, and any `cov` with
     `cov.IsLeviCivitaConnection` (or only `cov.IsMetricCompatible`, or only
     `cov.torsion = 0`, where that is all a lemma uses). These statements
     need no `letI`, apply to every Levi-Civita connection and not only to
     Mathlib's choice, and contain the page's hypotheses: `hJ` makes `σ`
     compatible with `J` (`compatible_of_inner_eq`), hence nondegenerate.
   - The milestones are stated in the page's form, for `hJ : σ.Compatible J`:
     inside the statement, `letI := hJ.riemannianBundle`, as `DESIGN.md`
     says, the connection is `CovariantDerivative.leviCivitaConnection I M`,
     and `⟪·, ·⟫` is the inner product of that instance, which is $g_J$. The
     `IsContMDiffRiemannianBundle` instance is
     `Compatible.isContMDiffRiemannianBundle`. The proof is the first layer,
     with `hJ` supplied by `Compatible.inner_riemannianBundle`.

   No definition bundles the connection of $g_J$: the milestones are the
   only statements that name it, and a definition would be a wrapper around
   `leviCivitaConnection` under the `letI`.
2. **Vector fields or tangent vectors.** Tangent vectors. All four
   quantities, $\nabla_uJ$, $\nabla\sigma$, $d\sigma$ and $N_J$, are tensors at
   a point in Mathlib and Tau Ceti (`hom … x`, `mextDeriv σ.val x`,
   `J.nijenhuis x`), the first milestone is stated at a point, and the
   identity of the second for vector fields is the pointwise one evaluated
   at their values. Vector fields enter only inside proofs: a tangent vector
   is extended to a smooth field by Tau Ceti's `exists_contMDiff_section_eq`
   or Mathlib's `FiberBundle.extend`, and the field formulas
   (`hom_apply`, `torsion_apply`, `mextDeriv_apply_two`) are read at the
   point.

Two further choices:

3. **$\nabla\sigma$ as a Hom-connection derivative.** $\nabla\sigma$ is
   `cov.hom (cov.hom (trivial ℝ)) σ.flat`, the two-form analogue of the
   `cov.hom (trivial F) α` of Tau Ceti's `ExteriorDerivative.lean` and of
   the private tensor of `Exterior/Two.lean`, rather than Tau Ceti's
   `CovariantDerivative.derivBilinearTensor`, whose argument order differs
   and which nothing below needs.
4. **The fourth identity is linear algebra.** Once the first three hold and
   $d\sigma=0$, the trilinear form $(u,v,w)\mapsto\langle(\nabla_uJ)v,w\rangle$ at
   a point is skew in its last two arguments, satisfies
   $\alpha(u,Jv,w)=\alpha(u,v,Jw)$, and has vanishing cyclic sum; any such form
   has $\alpha(Jv,w,z)=\alpha(v,w,Jz)$. This is a statement about Mathlib's
   linear maps only, so it gets its own small file,
   `LinearAlgebra/ComplexStructure/Trilinear.lean`, in the namespace
   `LinearMap`, beside the library's other files on linear complex
   structures, and not a private lemma of `LeviCivita.lean`.

`DESIGN.md` also makes *Hodge theory*'s use of this part conditional on
this file proving the Kähler identities through $\nabla J=0$. It does not:
the commutation relations of the Lefschetz operator and its adjoint with
$\partial$ and $\bar\partial$ are left to *Hodge theory*'s own design, which may use `Kahler.lean`'s
criterion if it proves them through $\nabla J=0$. No blocker changes
follow.

## Files

| File | Contents |
|---|---|
| `Geometry/Manifold/VectorBundle/CovariantDerivative/TwoForm.lean` | $d\sigma$ as the cyclic sum of $\nabla\sigma$ plus torsion terms, and without them for a torsion-free connection; namespace `CovariantDerivative` |
| `Geometry/Symplectic/Manifold/AlmostComplex/LeviCivita.lean` | the second, third and fourth identities, and the first milestone; namespace `TauCeti.SmoothAlmostComplexStructure`, the milestone in `TauCeti.SmoothTwoForm.Compatible` |
| `Geometry/Symplectic/Manifold/Kahler.lean` | the identity for $\langle N_J(u,v),w\rangle$, the equivalence of $\nabla J=0$ with $d\sigma=0$ and $N_J=0$, the Kähler form of it, and the second milestone; same namespaces |
| `LinearAlgebra/ComplexStructure/Trilinear.lean` | the algebraic step of the fourth identity; namespace `LinearMap` |

`TwoForm.lean` uses only Mathlib and Tau Ceti. `Trilinear.lean` uses only
Mathlib. `LeviCivita.lean` imports `TwoForm.lean`, `Trilinear.lean`,
*Almost complex manifolds*' `Metric.lean` and *Nijenhuis tensor*'s
`Covariant.lean`. `Kahler.lean` imports `LeviCivita.lean` and *Nijenhuis
tensor*'s `Nijenhuis.lean`.

## Definitions and their API

None. The part states its results with Mathlib's and Tau Ceti's objects:
`leviCivitaConnection`, `IsLeviCivitaConnection`, `CovariantDerivative.hom`,
`CovariantDerivative.trivial`, `SmoothTwoForm.flat`, `mextDeriv`,
`nijenhuis`, `IsClosed`, `IsKahler`, and `Compatible.metric`.

## Main results

### `Geometry/Manifold/VectorBundle/CovariantDerivative/TwoForm.lean`

For `covT : CovariantDerivative I E (TangentSpace I : M → Type _)`,
`σ : TauCeti.SmoothTwoForm I M`, `x : M` and `u v w : TangentSpace I x`,
with `D := covT.hom (covT.hom (CovariantDerivative.trivial ℝ)) σ.flat x`, so
that `D u v w` is $(\nabla_u\sigma)(v,w)$:

- `CovariantDerivative.mextDeriv_smoothTwoForm`:
  ```
  TauCeti.mextDeriv σ.val x ![u, v, w] =
    D u v w + D v w u + D w u v +
      σ.eval₂ x (covT.torsion x u v) w + σ.eval₂ x (covT.torsion x v w) u +
      σ.eval₂ x (covT.torsion x w u) v
  ```
  The two-form case of `mextDeriv_ofSubsingleton`. Proof: extend `u`, `v`,
  `w` to smooth fields, expand `D` by `hom_hom_apply`, `hom_apply` and
  `trivial_apply` (as Tau Ceti's private `hom_twoFormTensor_apply` does),
  the torsion by `torsion_apply`, and compare with
  `SmoothForm.mextDeriv_apply_two`.
- `CovariantDerivative.mextDeriv_smoothTwoForm_of_torsion_eq_zero`
  (`ht : covT.torsion x = 0`): `TauCeti.mextDeriv σ.val x ![u, v, w] =
  D u v w + D v w u + D w u v`.

About 150 lines. The module docstring credits Tau Ceti's
`exteriorCovariantDerivativeTwo_apply` and `hom_twoFormTensor_apply`,
whose steps the proof follows for scalar forms.

### `LinearAlgebra/ComplexStructure/Trilinear.lean`

- `LinearMap.apply_left_eq_apply_right_of_cyclic`: for a commutative semiring
  `R`, `R`-modules `V` and `W` with `[IsAddTorsionFree W]`,
  `j : V →ₗ[R] V` with `j ∘ₗ j = -LinearMap.id` and
  `α : V →ₗ[R] V →ₗ[R] V →ₗ[R] W` such that
  `α u (j v) w = α u v (j w)` and `α u v w + α v w u + α w u v = 0` for all
  `u v w`, it holds that `α (j v) w z = α v w (j z)` for all `v w z`.
  Proof: $D(v,w,z)=\alpha(jv,w,z)-\alpha(v,w,jz)$ is invariant under cyclic
  permutation (two applications of the cyclic sum and the rule for $j$),
  and $D(a,b,jc)=D(a,jb,c)=-D(ja,b,c)$; going once round the cycle gives
  $D(jv,w,z)=-D(jv,w,z)$, so $D$ vanishes on $jV=V$. About 60 lines.

### `Geometry/Symplectic/Manifold/AlmostComplex/LeviCivita.lean`

Variables: `[RiemannianBundle (fun x : M ↦ TangentSpace I x)]`,
`[IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]`,
`{σ} {J} {cov}`, `hJ : ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (J x v)`, and
`D := cov.hom cov J.toEndomorphism x`. In the namespace
`TauCeti.SmoothAlmostComplexStructure`:

- `inner_apply_left_of_inner_eq (hJ) x u w : ⟪J x u, w⟫ = σ.eval₂ x u w` and
  `inner_apply_left_eq_neg (hJ) x u w : ⟪J x u, w⟫ = -⟪u, J x w⟫`, the
  page's $\sigma(u,w)=\langle Ju,w\rangle$ and the skew-adjointness of $J$, are in
  *Almost complex manifolds*' `Metric.lean`, with the other consequences of
  `hJ`. The first is Tau Ceti's, in its `AlmostComplex/Metric.lean`, which
  `Metric.lean` imports; the library's copy of it was deleted by the move to
  `c9d170eed5a8` (#2025).
- `inner_hom_apply_eq_neg (hJ) (hcov : cov.IsMetricCompatible) x u v w :
  ⟪D u v, w⟫ = -⟪v, D u w⟫`: the second identity, from
  `IsMetricCompatible.inner_hom_eq_neg` and `inner_apply_left_eq_neg`.
- `hom_hom_flat_apply_eq_inner (hJ) (hcov : cov.IsMetricCompatible) x u v w :
  cov.hom (cov.hom (CovariantDerivative.trivial ℝ)) σ.flat x u v w = ⟪D u v, w⟫`:
  $(\nabla_u\sigma)(v,w)=\langle(\nabla_uJ)v,w\rangle$, from
  `inner_apply_left_of_inner_eq`, `hom_hom_apply`, `hom_apply` and metric
  compatibility on extended fields.
- `mextDeriv_apply_eq_inner (hJ) (hcov : cov.IsLeviCivitaConnection) x u v w`:
  ```
  TauCeti.mextDeriv σ.val x ![u, v, w] = ⟪D u v, w⟫ + ⟪D v w, u⟫ + ⟪D w u, v⟫
  ```
  the third identity, from `mextDeriv_smoothTwoForm_of_torsion_eq_zero`
  and the previous lemma.
- `hom_apply_eq_neg_comp (hJ) (hcov : cov.IsLeviCivitaConnection)
  (hσ : σ.IsClosed) x v : D (J x v) = -(J.toEndomorphism x).comp (D v)`:
  the fourth identity, from `LinearMap.apply_left_eq_apply_right_of_cyclic`
  for $\alpha(u,v,w)=\langle(\nabla_uJ)v,w\rangle$, whose hypotheses are
  the first identity (Tau Ceti's `CovariantDerivative.hom_apply_apply_anticomm`,
  with the differentiability of `J` from `Covariant.lean`) with the
  skew-adjointness of $J$, and the third identity with $d\sigma=0$.

In the namespace `TauCeti.SmoothTwoForm`, the milestone:

- `Compatible.leviCivita_hom_comp_add_and_inner_add_and_mextDeriv_and_apply
  (hJ : σ.Compatible J)`; the block below abbreviates the statement with `D`,
  which the theorem writes out in full:
  ```
  letI := hJ.riemannianBundle
  ∀ x (u v w : TangentSpace I x),
    let D := (CovariantDerivative.leviCivitaConnection I M).hom
      (CovariantDerivative.leviCivitaConnection I M) J.toEndomorphism x
    (D v).comp (J.toEndomorphism x) + (J.toEndomorphism x).comp (D v) = 0 ∧
    ⟪D u v, w⟫ + ⟪v, D u w⟫ = 0 ∧
    TauCeti.mextDeriv σ.val x ![u, v, w] = ⟪D u v, w⟫ + ⟪D v w, u⟫ + ⟪D w u, v⟫ ∧
    (σ.IsClosed → D (J x v) = -(J.toEndomorphism x).comp (D v))
  ```
  Milestone: *Levi-Civita derivative of a compatible almost complex
  structure*. The page's hypotheses are a nondegenerate `σ` and
  $J\in\mathcal J(M,\sigma)$; `σ.Compatible J` contains both
  (`Compatible.isNondegenerate`).

About 300 lines with `Trilinear.lean`.

### `Geometry/Symplectic/Manifold/Kahler.lean`

With the variables of `LeviCivita.lean`, in the namespace
`TauCeti.SmoothAlmostComplexStructure`:

- `inner_nijenhuis_eq (hJ) (hcov : cov.IsLeviCivitaConnection) x u v w`:
  ```
  ⟪J.nijenhuis x u v, w⟫ =
    TauCeti.mextDeriv σ.val x ![J x u, v, w] + TauCeti.mextDeriv σ.val x ![u, J x v, w] +
      2 * ⟪J x (D w u), v⟫
  ```
  equation (4.2.4), from the connection formula of `Nijenhuis.lean` and
  the first three identities. With $\alpha$ as above, both sides reduce to
  $\alpha(Ju,v,w)+\alpha(u,Jv,w)-\alpha(v,Ju,w)-\alpha(Jv,u,w)$, the
  terms $\alpha(w,Ju,v)$ and $\alpha(w,u,Jv)$ cancelling against the last
  summand.
- `hom_toEndomorphism_eq_zero_iff (hJ) (hcov : cov.IsLeviCivitaConnection) :
  cov.hom cov J.toEndomorphism = 0 ↔ σ.IsClosed ∧ J.nijenhuis = 0`. If
  $\nabla J=0$, the third identity gives $d\sigma=0$ and the connection
  formula $N_J=0$; conversely `inner_nijenhuis_eq` gives
  $\langle J(\nabla_wJ)u,v\rangle=0$ for all $v$, so $\nabla_wJ=0$.
- `hom_toEndomorphism_eq_zero_iff_isKahler (hJ) (hcov) :
  cov.hom cov J.toEndomorphism = 0 ↔ σ.IsKahler J`, by `isKahler_iff` and
  `compatible_of_inner_eq`.

In the namespace `TauCeti.SmoothTwoForm`:

- `Compatible.inner_nijenhuis_and_leviCivita_hom_eq_zero_iff (hJ : σ.Compatible J)`:
  ```
  letI := hJ.riemannianBundle
  let L := CovariantDerivative.leviCivitaConnection I M
  (∀ x (u v w : TangentSpace I x),
    ⟪J.nijenhuis x u v, w⟫ =
      TauCeti.mextDeriv σ.val x ![J x u, v, w] + TauCeti.mextDeriv σ.val x ![u, J x v, w] +
        2 * ⟪J x (L.hom L J.toEndomorphism x w u), v⟫) ∧
  (L.hom L J.toEndomorphism = 0 ↔ σ.IsClosed ∧ J.nijenhuis = 0)
  ```
  Milestone: *Parallel almost complex structures and the Kähler condition*,
  with $N_J=0$ in condition 2, as the page asks.
- `Compatible.leviCivita_hom_toEndomorphism_eq_zero_iff_isKahler
  (hJ : σ.Compatible J)`: under the same `letI`, `∇J = 0 ↔ σ.IsKahler J`.

About 250 lines.

## What it uses

- From Tau Ceti: `Compatible.metric` and `metric_inner` (`TauCeti/Geometry/Symplectic/Manifold/AlmostComplex/CompatibleMetric.lean`), in the
  milestone of `LeviCivita.lean`; `inner_apply_left_of_inner_eq`
  (`TauCeti/Geometry/Symplectic/Manifold/AlmostComplex/Metric.lean`), in its identities.
- From *Almost complex manifolds*: `Metric.lean` (#860), for `inner_apply_left_eq_neg`, in its
  identities.
- From *Nijenhuis tensor*: `Covariant.lean`, for the differentiability of
  `J` as a section of `End(TM)`, which Tau Ceti's $\nabla J$ and its
  anticommutation lemma `CovariantDerivative.hom_apply_apply_anticomm` take,
  in `LeviCivita.lean`; `Nijenhuis.lean`, for the formula of $N_J$
  through a torsion-free connection, in `Kahler.lean` (both #863, or the
  issue it splits off for `Covariant.lean`).
- From Tau Ceti and Mathlib: the declarations of *What there is*.

## Building issues

Each is a few hundred lines; each is blocked by the issues it names.

1. **$d$ of a two-form through a connection.** `TwoForm.lean`, all of it.
   About 150 lines. No blockers.
2. **The identities for $\nabla J$, and the first milestone.**
   `Trilinear.lean` and `LeviCivita.lean`. About 300 lines. Blocked by 1,
   by #860 (`Metric.lean`) and by #863 (`Covariant.lean`, or the issue
   that #863 splits off for it).
3. **The Kähler condition, and the second milestone.** `Kahler.lean`.
   About 250 lines. Blocked by 2 and by #863 (`Nijenhuis.lean`).

Issue 1 can start at once.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Lemma 4.1.14 (equations (4.1.9)–(4.1.12)), Proposition 4.2.1 and
  equation (4.2.4), Lemma 4.2.5.
* [A. Moroianu, *Lectures on Kähler Geometry*][Moroianu2007], Lemma 5.4
  and Theorem 5.5.
* [V. Apostolov and T. Drăghici, *The curvature and the integrability of
  almost-Kähler manifolds: a survey*][ApostolovDraghici2003], §3.3.
