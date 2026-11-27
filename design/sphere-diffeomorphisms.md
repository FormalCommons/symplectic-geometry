# Diffeomorphisms of the 2-sphere

This is the detailed design of part 46 of `DESIGN.md`, *Diffeomorphisms of
the 2-sphere*. It proves the two milestones of
`auxiliary/diffeomorphisms-of-the-2-sphere.md`: *Diffeomorphisms of the
2-sphere form a trivial principal bundle over the complex structures* and
*Smale's theorem on the diffeomorphism group of the 2-sphere*, the second by
the route through the first that the page proposes. The statement of the
first is the genus-zero case of Earle–Eells [EarleEells1967], Theorems 1 (a)
and 2 (a); the second is Smale's [Smale1959], Theorems A and 6. The input
on integrability is McDuff–Salamon [McDuffSalamon2017], Theorem 4.2.6, which
the library already has.

Paths of new files are under `SymplecticGeometry/`. Tau Ceti paths are
relative to `.lake/packages/TauCeti/TauCeti/`. Every Tau Ceti declaration
named below was checked against the pinned version `c9d170eed5a8`. All new
declarations are in the namespace `SymplecticGeometry`.

## Notation

- $S^2$ is `OnePoint ℂ` as a real surface, over the model `𝓘(ℝ, ℂ)`, and
  $i$ is `SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)`.
- $\omega_{FS}$ is Tau Ceti's `OnePoint.fubiniStudyForm`, compatible with
  $i$ (`OnePoint.compatible_fubiniStudyForm`).
- $\mathrm{Diff}(S^2)$ is `TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞` with the
  weak Whitney topology and its topological group structure
  (`Diffeomorph.weakWhitneyTopology`, `Diffeomorph.isTopologicalGroup`, both
  instances in the scope `TauCeti.DiffeomorphWeakWhitney`). Its product is
  composition, $\phi\psi=\phi\circ\psi$ (`Diffeomorph.coe_mul`).
- The pull-back $\phi^*J$ is Tau Ceti's
  `SmoothAlmostComplexStructure.pullback φ J`, whose value at $x$ is
  $(d\phi_x)^{-1}J_{\phi(x)}\,d\phi_x$ (`pullback_apply`): the page's
  convention.
- $\mathcal J$ is the subtype `{J // OnePoint.fubiniStudyForm.Tames J}` (`𝒥`, a
  local notation, in Lean statements below), the structures tamed by
  $\omega_{FS}$, with Tau Ceti's
  `SmoothAlmostComplexStructure.frameTopology e U hU` for a covering frame
  system (`hcover : ∀ x, ∃ k, x ∈ U k`). Statements about the topology of
  $\mathcal J$ hold for every such system, as in part 45; by
  `frameTopology_eq_of_covers` the choice does not matter.
- $E_J$, for $J\in\mathcal J$, is part 45's `twistOneKernel J`, the smooth
  sections of $L=\mathcal O(1)$ (`OnePoint.twistCore 1`, whose fibres are
  `ℂ`) killed by $D_J$.

## What there is, and what is missing

Tau Ceti has the groups and their topologies, the Möbius group with its
topology and its polar retraction, and the comparison of `OnePoint ℂ` with
the round sphere.

- **Diffeomorphism groups.** `TauCeti.Diff` (`Geometry/Diffeomorphism/Group.lean`);
  the weak Whitney topology with `continuous_weakWhitney_iff`,
  `continuous_eval_const` and `ContMDiff.continuous_diffeomorphWeakWhitney`
  (`Topology.lean`); `Diffeomorph.isTopologicalGroup` (`Inversion.lean`);
  conjugation by a diffeomorphism as an isomorphism of topological groups,
  `Diffeomorph.diffCongrContinuousMulEquiv` (`Congr.lean`).
- **Orientations.** `Diffeomorph.orientationPreservingSubgroup`
  (`Geometry/Manifold/Orientation/Preserving.lean`), the subgroup of
  diffeomorphisms preserving a `TauCeti.Manifold.Orientation` at every point;
  the orientation of a complex manifold, `TauCeti.complexManifoldOrientation`
  (`Geometry/Manifold/Complex/Orientation.lean`); the orientation of a
  round sphere, `Orientation.sphereOrientation`, and its pull-back along
  `OnePoint.diffeomorphSphere` (`Geometry/Manifold/Instances/OnePoint/Sphere.lean`);
  pseudoholomorphic maps preserve the orientations of their complex frames,
  `IsPseudoholomorphicAt.isOrientationPreservingAt`
  (`Geometry/Symplectic/Manifold/AlmostComplex/Orientation.lean`).
- **Almost complex structures.** `SmoothAlmostComplexStructure.pullback`,
  `eq_pullback_iff`, `pullback_trans`, `isPseudoholomorphic_pullback` and
  `Tames.pullback` (`Geometry/Symplectic/Manifold/AlmostComplex/Pullback.lean`);
  `frameTopology`, `continuous_frameTopology_iff` and
  `isOpen_setOf_tames_frameTopology` (`…/Topology.lean`); the Cayley path
  `SmoothTwoForm.Compatible.cayleyPath` from a compatible to a tame
  structure, with `tames_cayleyPath`, `cayleyPath_of_nonpos`,
  `cayleyPath_of_one_le` and `cayleyPath_self` (`…/CayleyPath.lean`);
  holomorphic maps are the pseudoholomorphic maps for the structures of
  complex manifolds, `isPseudoholomorphic_ofComplexManifold_iff`
  (`Geometry/Manifold/Complex/AlmostComplexStructure.lean`), and complex
  differentiable maps are smooth, `MDifferentiable.contMDiff`
  (`Geometry/Manifold/Complex/Analytic.lean`).
- **Möbius transformations.** The actions of `GL (Fin 2) ℂ` and `PSL(2, ℂ)`
  on `OnePoint ℂ` by maps of the real surface,
  `OnePoint.instContMDiffConstSMulGLReal` and
  `OnePoint.instContMDiffConstSMulPSLReal` (`Instances/OnePoint/Moebius.lean`),
  with `Diffeomorph.constSmul` (`Geometry/Manifold/Algebra/SMul.lean`);
  joint continuity, `OnePoint.instContinuousSMulPSL` (`…/ContinuousSMul.lean`);
  every biholomorphism is Möbius, `Diffeomorph.exists_coe_eq_smul`, and by
  `Diffeomorph.eq_refl_of_apply_zero_one_infty_eq_self` only the identity
  fixes $0$, $1$ and $\infty$ (`…/Automorphism.lean`);
  `PSL(2, ℂ)` is homeomorphic to the triples of distinct points,
  `OnePoint.pslHomeomorphDistinctTriples` (`…/DistinctTriples.lean`).
- **The rotation group.** The polar strong deformation retraction of
  `PSL(n, 𝕜)` onto `PSU(n)`, `Matrix.ProjectiveSpecialLinearGroup.polarHomotopy`,
  a `HomotopyRel` from the identity to `polarRetraction`
  (`Analysis/Matrix/Polar/SpecialLinear.lean`); `PSU(2) ≃ₜ* SO(3)`,
  `TauCeti.SU2.psuEquivSO3` with `psuEquivSO3_rangeRestrict`
  (`Topology/Algebra/Matrix/ProjectiveSpecialLinearGroup/RotationGroup.lean`);
  the round sphere coordinates `OnePoint.sphereCoords`, which intertwine
  `PSU(2)` with `SU2.toSO3`, `Matrix.specialUnitaryGroup.sphereCoords_toPSL_smul`,
  and the formula `OnePoint.sphereCoords_coe` (`Instances/OnePoint/RoundSphere.lean`);
  the analytic diffeomorphism `OnePoint.diffeomorphSphere v ι` onto the unit
  sphere, with `coe_diffeomorphSphere_coe` and `diffeomorphSphere_infty`
  (`Instances/OnePoint/Sphere.lean`); the inclusion
  `TauCeti.orthogonalToDiffSphere` with `continuous_orthogonalToDiffSphere`
  (`Geometry/Diffeomorphism/Sphere.lean`); and
  `TauCeti.specialOrthogonalGroupFundamentalGroupMulEquiv`
  (`Topology/Algebra/CliffordAlgebra/Spin/UniversalCover.lean`).
- **Local diffeomorphisms.** `isLocalDiffeomorphAt_of_injective_mfderiv`
  (`Geometry/Manifold/LocalDiffeomorph/Basic.lean`) and Mathlib's
  `IsLocalDiffeomorph.diffeomorphOfBijective`.
- **This library.** The continuity of the Cayley path in the frame topology,
  `Bundle.continuous_fiberwiseMap_cayleyPathFormula`, and its use for the
  tangent bundle in `Geometry/Symplectic/Manifold/AlmostComplex/Contractible.lean`
  (*Symplectic vector bundles*); and, from part 45, the operators $D_J$,
  $\dim_{\mathbb C}E_J=2$, the zero count, and the continuous family of the
  $E_J$ (`design/cauchy-riemann-sphere.md`, files `Basic.lean` and
  `Kernel.lean` of `Geometry/Manifold/Instances/OnePoint/CauchyRiemann/`).

Missing, and built here: the subgroup $\mathrm{Diff}^+(S^2)$ with its map to
$\mathcal J$; the contraction of $\mathcal J$ fixing $i$; the Möbius group
as a subgroup of $\mathrm{Diff}(S^2)$, its identification with the
stabilizer of $i$ and with `PSL(2, ℂ)` as topological groups; the map
$\sigma$ and its continuity; the trivialization; and the retraction onto
$\mathrm{SO}(3)$ with its transport to the round sphere.

## Decisions

These settle the points of *The design file decides* of part 46, and the
notes of the approving review of #2280.

1. **$\mathrm{Diff}^+(S^2)$ by Tau Ceti's orientations.** `diffPlus` is
   `Diffeomorph.orientationPreservingSubgroup` for
   `TauCeti.complexManifoldOrientation ℂ (OnePoint ℂ)`. The degree is not
   used: preserving the orientation at every point is what the trivialization
   needs, since it gives at once that $\phi^*i$ is tamed by $\omega_{FS}$ and
   conversely (`mem_diffPlus_iff_tames_pullback`). On a surface a $2$-form
   is a multiple of $\omega_{FS}$ at each point, and
   $\omega_{FS}(v,\phi^*i\,v)=((\phi^{-1})^*\omega_{FS})(d\phi\,v,\,i\,d\phi\,v)$,
   which is positive exactly when $\phi^{-1}$, hence $\phi$, preserves the
   orientation at the points involved.
2. **$\mathcal J$ is the set of structures tamed by $\omega_{FS}$**, as the
   conventions *Fibrations, connections and diffeomorphism groups* and part
   45 take it, with $\sigma=\omega_{FS}$ in part 45's statements.
3. **The pull-back is continuous in $\phi$ for a fixed $J$.** Only
   $p(\phi)=\phi^*i$ is used: the trivialization and the deformation never
   pull a varying structure back. Joint continuity in $(\phi,J)$ would need
   continuity of composition $J\circ\phi$ in the $C^\infty$ topologies, and
   nothing uses it, so it is not built.
4. **The contraction of $\mathcal J$ is the Cayley path from $i$**, not the
   rescaling of the Beltrami coefficient that the page mentions; at each
   point the two are the same kind of radial contraction of the disc of
   tame structures onto its centre. Tau Ceti's
   `Compatible.cayleyPath compatible_fubiniStudyForm hJ (1 - t)` runs from
   $J$ at $t=0$ to $i$ at $t=1$ inside $\mathcal J$ (`tames_cayleyPath`), and
   is $i$ at every time when $J=i$ (`cayleyPath_self`), as the review note
   asks. Joint continuity in $(t,J)$ is that of
   `Bundle.continuous_fiberwiseMap_cayleyPathFormula`, carried to the tangent
   bundle as `AlmostComplex/Contractible.lean` does.
5. **$\sigma(J)$ is built without a complex atlas for $J$.** Tau Ceti's
   `TauCeti.RiemannSurface.biholomorphOfDegreeEqOne` would need $(S^2,J)$
   as a complex manifold, that is, a holomorphic atlas from isothermal
   charts of $J$, which nothing else here needs. Instead, take
   $s_0,s_\infty\in E_J\setminus\{0\}$ with $s_0(0)=0$ and $s_\infty(\infty)=0$:
   - the map $\sigma(J)(x)=[s_0(x)s_\infty(1):s_\infty(x)s_0(1)]$ is defined
     through `OnePoint.equivProjectivization`, and does not depend on the
     choice of $s_0,s_\infty$, because the sections of $E_J$ vanishing at a
     point form a complex line (two independent ones would give a
     combination with two zeros);
   - where $s_\infty\ne0$, write $s_0=u\,s_\infty$; the Leibniz rule of the
     real Cauchy–Riemann operator $D_J$, which is complex linear
     (`isRealCauchyRiemannOperator_twistOneDelBar` and
     `isComplexLinearOperator_twistOneDelBar` of part 45), gives
     $0=D_Js_0=(\bar\partial_Ju)\,s_\infty$, so $u$ is $J$-holomorphic; the
     same holds for $s_\infty/s_0$ where $s_0\ne0$. So $d\sigma(J)\circ J=
     i\circ d\sigma(J)$, which is $\sigma(J)^*i=J$ once $\sigma(J)$ is a
     diffeomorphism (`eq_pullback_iff`);
   - at a point $x$ with $\sigma(J)(x)=c\in\mathbb C$, the section
     $s_0-c'\,s_\infty$ with $c'=c\,s_0(1)/s_\infty(1)$ vanishes at $x$, and
     its zero is simple (part 45's zero count), so $du(x)$ is invertible;
     at $x=\infty$ the same holds for $s_\infty/s_0$. So $\sigma(J)$ is a
     local diffeomorphism (`isLocalDiffeomorphAt_of_injective_mfderiv`);
   - it is injective, since $\sigma(J)(x)=\sigma(J)(y)$ makes one nonzero
     element of $E_J$ vanish at $x$ and at $y$; and surjective, since its
     image is open, compact and nonempty in the connected sphere;
   - so it is a diffeomorphism (`IsLocalDiffeomorph.diffeomorphOfBijective`).
   This is the page's step 3, with the degree argument replaced by the zero
   count of part 45, which already gives that each zero is simple.
6. **The bridge between the real and the complex settings** is
   `pullback_eq_self_iff`: a real diffeomorphism $\phi$ of the sphere has
   $\phi^*i=i$ exactly when it is a Möbius transformation of `PSL(2, ℂ)`.
   One way: $\phi^*i=i$ makes $\phi$ and $\phi^{-1}$ pseudoholomorphic for
   $i$ (`isPseudoholomorphic_pullback`), hence complex differentiable
   (`isPseudoholomorphic_ofComplexManifold_iff`) and smooth over `ℂ`
   (`MDifferentiable.contMDiff`), so a complex diffeomorphism, which is
   $x\mapsto g\cdot x$ for some `g : GL (Fin 2) ℂ`
   (`Diffeomorph.exists_coe_eq_smul`); dividing a matrix by a square root of
   its determinant gives an element of `SL(2, ℂ)` with the same action. The
   other way: a Möbius transformation is holomorphic, and a holomorphic map
   has a complex linear derivative.
7. **Uniqueness of $\sigma(J)$** comes from
   `Diffeomorph.eq_refl_of_apply_zero_one_infty_eq_self` applied to
   $\phi\circ\sigma(J)^{-1}$, which pulls $i$ back to $i$ and so is Möbius by
   Decision 6. The review note suggests
   `Diffeomorph.existsUnique_apply_eq_zero_one_infty`, but that statement
   is about a complex manifold biholomorphic to the sphere, and $(S^2,J)$ is
   not given a complex structure here (Decision 5); its proof is the same
   reduction to `eq_refl_of_apply_zero_one_infty_eq_self`.
8. **The Möbius group is the stabilizer of $i$ in $\mathrm{Diff}(S^2)$**,
   `mobiusSubgroup`, with the subspace topology, as on the page. It is the
   range of `mobiusHom : PSL(2, ℂ) →* Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞`,
   $g\mapsto$ `Diffeomorph.constSmul 𝓘(ℝ, ℂ) ∞ g`, by Decision 6, and lies in
   `diffPlus` by Decision 1. Its subspace topology is that of `PSL(2, ℂ)`
   (`mobiusEquiv : PSL(2, ℂ) ≃ₜ* mobiusSubgroup`): continuity of
   `mobiusHom` comes from the smooth action of `GL (Fin 2) ℂ`, an open
   subset of the matrices, through `ContMDiff.continuous_diffeomorphWeakWhitney`,
   descended to `PSL(2, ℂ)` by its quotient topology; continuity of the
   inverse comes from the evaluations at $0,1,\infty$, which are continuous
   (`continuous_eval_const`), followed by the inverse of
   `OnePoint.pslHomeomorphDistinctTriples`. No Lie group structure on
   `PSL(2, ℂ)` is needed: its topology is Tau Ceti's quotient topology.
9. **The round sphere.** Smale's theorem is stated, as on the page, for the
   unit sphere `sphere (0 : EuclideanSpace ℝ (Fin 3)) 1` with model `𝓡 2`,
   oriented by `Orientation.sphereOrientation` of the standard orientation of
   `EuclideanSpace ℝ (Fin 3)`, and for $\mathrm{SO}(3)$ as
   `Matrix.specialOrthogonalGroup (Fin 3) ℝ` acting through
   `TauCeti.orthogonalToDiffSphere 2 ∞`. It is carried over from `OnePoint ℂ`
   by conjugation, `Diffeomorph.diffCongrContinuousMulEquiv`, along
   `roundSphereDiffeomorph := OnePoint.diffeomorphSphere v ι`, with $v$ the
   north pole and $\iota\,z=(\operatorname{Re}z,-\operatorname{Im}z,0)$. With
   this choice its underlying map is `OnePoint.sphereCoords`
   (`coe_roundSphereDiffeomorph`, from `sphereCoords_coe` and
   `coe_diffeomorphSphere_coe`), so the conjugate of the Möbius
   transformation of `toPSL k` is the rotation `SU2.toSO3 k`
   (`sphereCoords_toPSL_smul`). The review note proposes `pauliRotation`,
   which is the same intertwining for `U(2)`; through `PSL(2, ℂ)` it is
   `SU2.toSO3` and `psuEquivSO3` that apply. The conjugate of `diffPlus` is
   the orientation-preserving subgroup of the round sphere, because the
   pull-back of `sphereOrientation` along `roundSphereDiffeomorph` is
   $\pm$`complexManifoldOrientation` (from the comparison of the two at each
   point in Tau Ceti's `OnePoint/Sphere.lean`, on the connected sphere), and
   a map preserves an orientation exactly when it preserves its opposite.
10. **"Strong deformation retract"** is Mathlib's
    `ContinuousMap.HomotopyRel`, the form of Tau Ceti's
    `ProjectiveSpecialLinearGroup.polarHomotopy`: a homotopy relative to the
    subgroup $S$ of rotations from the identity of $\mathrm{Diff}^+$ to a
    retraction $r$ onto $S$ followed by the inclusion. The consequences on
    the page follow from it: the inclusion $\mathrm{SO}(3)\to\mathrm{Diff}^+$
    is a homotopy equivalence (`ContinuousMap.HomotopyEquiv`, with that
    inclusion as its map, in the form of Tau Ceti's `TauCeti.SmaleConjecture`),
    $\mathrm{Diff}^+$ is path connected, and its fundamental group at $1$ is
    `Multiplicative (ZMod 2)`, through
    `specialOrthogonalGroupFundamentalGroupMulEquiv 3`. The issue uses the
    invariance of fundamental groups under a homotopy equivalence that fixes
    the base point that Mathlib or Tau Ceti has, and searches for it first.
11. **The deformation of $\mathrm{Diff}^+(S^2)$** is, with $\Phi$ the
    trivialization, $c_t$ the contraction of Decision 4 and $m_t$ the polar
    homotopy carried to `mobiusSubgroup` by `mobiusEquiv`,
    $H_t(\phi)=\Phi^{-1}(c_t(\phi^*i),\,m_t(\Phi(\phi)_2))$. For a rotation
    $\phi$, $\phi^*i=i$ and $\sigma(i)=1$ (Decision 7), so
    $\Phi(\phi)=(i,\phi)$ and $H_t(\phi)=\phi$; and
    $H_1(\phi)=m_1(\Phi(\phi)_2)\,\sigma(i)$ is a rotation.

## Departures from `DESIGN.md`

The overview's part 46 is corrected in the same pull request where this file
departs from it or where the review of #2280 asked for a fix:
`ComplexStructure.lean` proves the continuity of the pull-back in $\phi$
only (Decision 3); `Uniformization.lean` does not use
`TauCeti.RiemannSurface.biholomorphOfDegreeEqOne` (Decision 5), which is
also taken out of the existing inputs of the first milestone in the
milestone table; and the wording on the name of `Smale.lean` is fixed: the
file lies in `Geometry/Diffeomorphism/Sphere/`, while Tau Ceti's
`Geometry/Diffeomorphism/Smale.lean`, whose name it shares, states the
Smale conjecture for $S^3$. No dependency between parts changes.

## Files and their contents

All files are in `Geometry/Diffeomorphism/Sphere/`, beside Tau Ceti's
`Covered.lean`, `Isotopy.lean` and `RotationFamily.lean` of that folder; no
Tau Ceti file has their names.

| File | Contents | Issues |
|---|---|---|
| `ComplexStructure.lean` | `diffPlus`, $\mathcal J$, $p$, the contraction | 1, 2 |
| `Mobius.lean` | `mobiusHom`, `mobiusSubgroup`, the bridge, the topology, the rotations | 3, 4 |
| `Uniformization.lean` | $\sigma(J)$, its properties, its continuity | 5, 6 |
| `Trivialization.lean` | the homeomorphism and the first milestone | 7 |
| `Smale.lean` | the round sphere, the retraction and the second milestone | 8, 9 |

### `ComplexStructure.lean`

Issue 1:

- `diffPlus : Subgroup (TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞)`, Decision 1,
  with `mem_diffPlus_iff`.
- `𝒥`, the subtype of the structures tamed by `OnePoint.fubiniStudyForm`,
  and `tameOfComplexManifold : 𝒥`, the structure $i$.
- `mem_diffPlus_iff_tames_pullback : φ ∈ diffPlus ↔ fubiniStudyForm.Tames (i.pullback φ)`
  (`φ : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞`).
- `complexStructureMap : diffPlus → 𝒥`, $\phi\mapsto\phi^*i$,
  with `coe_complexStructureMap`, `complexStructureMap_mul`
  ($(\phi\psi)^*i=\psi^*(\phi^*i)$, from `pullback_trans`) and
  `continuous_complexStructureMap` for every covering frame system
  (Decision 3). The continuity reads the frame coefficients of
  $\phi^*i$ through the chart derivatives of $\phi$ and of $\phi^{-1}$,
  using `continuous_manifoldWeakWhitney_iff_compact_chartIteratedFDeriv`
  (`Geometry/Manifold/ContMDiffMap/Chart/Topology.lean`) and the continuity
  of inversion.

About 350 lines.

Issue 2:

- `complexStructureContraction : (ContinuousMap.id 𝒥).HomotopyRel (ContinuousMap.const _ i) {i}`,
  for every covering frame system, from the Cayley path (Decision 4), with
  `complexStructureContraction_apply`.

About 200 lines.

### `Mobius.lean`

Issue 3:

- `mobiusHom : PSL(2, ℂ) →* TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞`, with
  `mobiusHom_apply : mobiusHom g x = g • x` and `mobiusHom_injective`
  (from `OnePoint.existsUnique_psl_smul_zero_one_infty_eq`).
- `mobiusSubgroup`, the `φ` with `φ.pullback i = i`, with
  `mem_mobiusSubgroup_iff`.
- `pullback_eq_self_iff : φ.pullback i = i ↔ ∃ g, φ = mobiusHom g`
  (Decision 6), and `mobiusSubgroup_eq_range : mobiusSubgroup = mobiusHom.range`.

About 300 lines.

Issue 4:

- `mobiusEquiv : PSL(2, ℂ) ≃ₜ* mobiusSubgroup`, with
  `coe_mobiusEquiv_apply` (Decision 8).
- `rotationSubgroup : Subgroup (TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞)`, the
  image of `PSU(2)` (the range of `Matrix.specialUnitaryGroup.toPSL`) under
  `mobiusHom`, with `rotationSubgroup_le_mobiusSubgroup`.
- `mobiusPolarHomotopy`, the polar homotopy
  `ProjectiveSpecialLinearGroup.polarHomotopy (Fin 2) ℂ` carried to
  `mobiusSubgroup` by `mobiusEquiv`: a homotopy relative to the rotations
  from the identity to a retraction onto them.

About 250 lines.

### `Uniformization.lean`

Issue 5 (for `J : 𝒥`; part 45's results with
$\sigma=\omega_{FS}$):

- `exists_mem_twistOneKernel_eq_zero`: every point is the zero of some
  nonzero element of $E_J$; and the elements vanishing at a given
  point form a complex line.
- `uniformizingMap J : OnePoint ℂ → OnePoint ℂ`, Decision 5, with
  `uniformizingMap_eq` (any choice of $s_0,s_\infty$ gives it) and its values
  at `0`, `1` and `∞`.
- `isLocalDiffeomorph_uniformizingMap`, `bijective_uniformizingMap`, and
  `uniformizingDiffeomorph J : diffPlus` with
  `pullback_uniformizingDiffeomorph : (uniformizingDiffeomorph J).pullback i = J`.
  The $J$-holomorphy of the ratio of two elements of $E_J$ is a lemma of its
  own, `isPseudoholomorphicOn_div_of_mem_twistOneKernel`.
- `eq_uniformizingDiffeomorph_iff`: an element of `diffPlus` equals
  `uniformizingDiffeomorph J` exactly when it pulls $i$ back to $J$ and
  fixes `0`, `1` and `∞` (Decision 7); and
  `uniformizingDiffeomorph_ofComplexManifold : uniformizingDiffeomorph i = 1`.

About 450 lines.

Issue 6:

- `continuous_uniformizingDiffeomorph`: for every covering frame system,
  `J ↦ uniformizingDiffeomorph J` is continuous from $\mathcal J$ to
  `diffPlus`. At each $J_0$, part 45's family $T_J$ of isomorphisms
  $E_{J_0}\to E_J$ (`exists_continuousAt_twistOneKernelFamily`) gives
  $s_0(J)=\lambda_J(b)T_Ja-\lambda_J(a)T_Jb$ with $\lambda_J=\mathrm{ev}_0\circ T_J$
  for a basis $a,b$ of $E_{J_0}$, nonzero near $J_0$, and likewise
  $s_\infty(J)$; both are continuous at $J_0$ in the $C^\infty$ topology of
  sections. The map from pairs of smooth sections of $L$ without common
  zero to smooth maps $S^2\to S^2$, $(s,s')\mapsto[s\,s'(1):s'\,s(1)]$, is
  continuous into the weak Whitney topology: in the affine and in the
  inverted frame of $L$ it is composition with a smooth map, and
  `continuous_comp_manifoldWeakWhitney` (`ContMDiffMap/Chart/Comp.lean`)
  applies on each frame domain. That $\lambda_J\neq0$ uses only that no
  nonzero element of $E_J$ has two zeros.

About 350 lines.

### `Trivialization.lean`

Issue 7:

- `mobiusSubgroup_le_diffPlus` (Decision 1).
- `diffPlusTrivialization : diffPlus ≃ₜ 𝒥 × mobiusSubgroup`,
  for every covering frame system, $\phi\mapsto(\phi^*i,\ \phi\,\sigma(\phi^*i)^{-1})$,
  with inverse $(J,g)\mapsto g\,\sigma(J)$; `diffPlusTrivialization_apply_fst`,
  `coe_diffPlusTrivialization_apply_snd`, `coe_diffPlusTrivialization_symm_apply`,
  and `diffPlusTrivialization_mul`: left multiplication by
  $g\in$ `mobiusSubgroup` is left multiplication on the second factor.
- The milestone, `exists_continuous_section_homeomorph_prod_mobiusSubgroup`:
  `uniformizingDiffeomorph` is a continuous section of `complexStructureMap`;
  each value is the unique element of `diffPlus` over $J$ fixing `0`, `1`,
  `∞`; and there is a homeomorphism `diffPlus ≃ₜ 𝒥 × mobiusSubgroup`
  whose first component is `complexStructureMap`, whose second is
  $\phi\,\sigma(\phi^*i)^{-1}$, and whose inverse is $(J,g)\mapsto g\,\sigma(J)$.
  Its docstring ends with the milestone line for *Diffeomorphisms of the
  2-sphere form a trivial principal bundle over the complex structures*.

About 250 lines.

### `Smale.lean`

Issue 8:

- `roundSphereDiffeomorph`, Decision 9, with `coe_roundSphereDiffeomorph`
  (its values are `OnePoint.sphereCoords`, read in `EuclideanSpace ℝ (Fin 3)`).
- `roundDiffPlus`, the orientation-preserving subgroup of the round sphere
  for `sphereOrientation`, and `map_diffPlus_diffCongr`: conjugation by
  `roundSphereDiffeomorph` maps `diffPlus` onto `roundDiffPlus`.
- `diffCongr_mobiusHom_toPSL`: conjugation sends `mobiusHom (toPSL k)` to
  `orthogonalToDiffSphere 2 ∞ (SU2.toSO3 k)`; hence it maps
  `rotationSubgroup` onto the image of `Matrix.specialOrthogonalGroup (Fin 3) ℝ`
  (`TauCeti.SU2.toSO3_surjective`), which therefore lies in `roundDiffPlus`.

About 300 lines.

Issue 9:

- `diffPlusPolarHomotopy`: the homotopy of Decision 11 on `diffPlus`,
  relative to the rotations, ending in them.
- The milestone, `exists_homotopyRel_specialOrthogonal_roundDiffPlus`:
  there are a retraction $r$ of `roundDiffPlus` onto the image of
  $\mathrm{SO}(3)$ and a `HomotopyRel` relative to that image from the
  identity to $r$ followed by the inclusion (Decision 10). Its docstring ends
  with the milestone line for *Smale's theorem on the diffeomorphism group
  of the 2-sphere*.
- `specialOrthogonalHomotopyEquivRoundDiffPlus`: the inclusion
  $\mathrm{SO}(3)\to$ `roundDiffPlus` is the map of a homotopy equivalence;
  `pathConnectedSpace_roundDiffPlus`; and
  `roundDiffPlusFundamentalGroupMulEquiv : FundamentalGroup roundDiffPlus 1 ≃* Multiplicative (ZMod 2)`.

About 300 lines.

## What the part uses

- Tau Ceti, as listed under *What there is*.
- Part 45, *Cauchy–Riemann operators on the sphere*: the operator $D_J$ and
  its Leibniz rule, $E_J$ with $\dim_{\mathbb C}E_J=2$, the zero count
  (each nonzero element of $E_J$ has one zero, which is simple), and the
  continuous family of the $E_J$, as `design/cauchy-riemann-sphere.md`
  names them. The building issues follow that file's names.
- This library: *Symplectic vector bundles* (the continuity of the Cayley
  path, Decision 4).
- Mathlib: `ContinuousMap.HomotopyRel`, `ContinuousMap.HomotopyEquiv`,
  `FundamentalGroup`, `IsLocalDiffeomorph.diffeomorphOfBijective`.

## Building issues

In this order. All are sub-issues of #2383, *Build the part Diffeomorphisms
of the 2-sphere*. Sizes are estimates. "P45" stands for #2371, *Build the
part Cauchy–Riemann operators on the sphere*, or, once it is split, for its
issues that build the results named.

| # | Issue | Files | Blocked by | Size |
|---|---|---|---|---|
| 1 | $\mathrm{Diff}^+(S^2)$, the space $\mathcal J$ and the map $\phi\mapsto\phi^*i$ | `ComplexStructure.lean` | — | 350 |
| 2 | The contraction of $\mathcal J$ onto $i$ | `ComplexStructure.lean` | 1 | 200 |
| 3 | Möbius transformations as the stabilizer of $i$ | `Mobius.lean` | — | 300 |
| 4 | The Möbius group as a topological group, and its retraction onto the rotations | `Mobius.lean` | 3 | 250 |
| 5 | The uniformizing diffeomorphism $\sigma(J)$ | `Uniformization.lean` | 1, 3; P45 (zero count, $\dim E_J=2$) | 450 |
| 6 | Continuity of $\sigma$ | `Uniformization.lean` | 5; P45 (continuous family) | 350 |
| 7 | The trivialization of $\mathrm{Diff}^+(S^2)$ over $\mathcal J$ | `Trivialization.lean` | 6 | 250 |
| 8 | The round sphere: $\mathrm{Diff}^+$ and the rotations | `Smale.lean` | 1, 4 | 300 |
| 9 | Smale's theorem | `Smale.lean` | 2, 7, 8 | 300 |

Issues 1 and 3 can start at once. The milestones are proved in issues 7
and 9.

## References

* [S. Smale, *Diffeomorphisms of the 2-sphere*][Smale1959], Theorems A
  and 6.
* [C. J. Earle, J. Eells, *The diffeomorphism group of a compact Riemann
  surface*][EarleEells1967], Theorems 1 (a) and 2 (a).
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd
  ed.][McDuffSalamon2017], Theorem 4.2.6 and p. 164 (complex structures on
  a surface), Lemma 6.2.3 (the use of Smale's theorem).
