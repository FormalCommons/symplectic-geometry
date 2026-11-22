# Hamiltonian flows

The detailed design of part 15 of `DESIGN.md`, *Hamiltonian flows*. It
proves three milestones of `atlas/symplectic-manifolds.md`: *Symplectic
vector fields and isotopy generators*, *Hamiltonian flows and the Poisson
algebra* and *Hamiltonian isotopies and their composition*. It follows
McDuff–Salamon [McDuffSalamon2017], §3.1: Proposition 3.1.5, Remark 3.1.6,
Proposition 3.1.10 and the discussion after it, Definition 3.1.13,
Exercise 3.1.14 and Remark 3.1.15, with the correction to p. 100 in
[McDuffSalamon2019Errata].

All declarations of Tau Ceti and Mathlib named below were checked against the
pinned versions (Tau Ceti `v4.37.0-rc1`, see `lakefile.toml`). Paths of Tau
Ceti files are relative to `.lake/packages/TauCeti/TauCeti/`.

## What there is, and what is missing

Tau Ceti already has most of the vector-field calculus and the Hamiltonian
group. Below, `σ : TauCeti.SmoothTwoForm J M` is a two-form on a manifold
`M` modelled on `J : ModelWithCorners ℝ E H`.

- **Symplectic vector fields** (`Geometry/Symplectic/Hamiltonian/SymplecticVectorField.lean`):
  the submodule `σ.symplecticVectorFields` of smooth sections
  `Cₛ^∞⟮J; E, TangentSpace J (M := M)⟯` with closed contraction, with
  `mem_symplecticVectorFields_iff` ($d(\iota_X\sigma)=0$) and, for closed
  `σ`, `mem_symplecticVectorFields_iff_mlieDerivForm_eq_zero`
  ($\mathcal L_X\sigma=0$); the contraction `σ.interiorₗ` and the class map
  `σ.interiorClass`.
- **Flows preserving forms** (`Geometry/Manifold/DifferentialForm/Flow.lean`):
  `TauCeti.mpullback_flowOf_apply_of_mextDeriv_interior_eq_zero` (the local
  flow of a field with closed contraction preserves a closed form wherever
  it is defined) and `TauCeti.hasDerivAt_mpullback_flowOf_zero` (the Lie
  derivative is the time derivative of the pulled-back forms at time $0$).
  Both assume `[FiniteDimensional ℝ E] [J.Boundaryless] [T2Space M]`.
- **Isotopies over `ℝ`** (`Geometry/Manifold/DifferentialForm/Flow/Eulerian.lean`):
  `TauCeti.forall_mpullback_eq_iff_forall_mextDeriv_interior_eulerianField_eq_zero`,
  for a family `φ : ℝ → M ≃ M` whose maps and inverses are jointly `C²`: the
  pullbacks of a closed form are independent of time exactly when every
  contraction with `TauCeti.eulerianField J φ t` is closed.
- **Brackets** (`Geometry/Symplectic/Hamiltonian/Bracket.lean`):
  `TauCeti.SmoothTwoForm.isHamiltonianVectorField_mlieBracket` (for closed
  `σ` and smooth symplectic `X`, `Y`, the bracket `mlieBracket J X Y` is a
  Hamiltonian vector field of $\sigma(Y,X)$), `IsNondegenerate.hamiltonianVectorField_poissonBracket`
  ($X_{\{f,g\}}=-[X_f,X_g]$ with Mathlib's bracket),
  `IsNondegenerate.poissonBracket_jacobi`.
- **Hamiltonian vector fields and the Poisson bracket**
  (`Geometry/Symplectic/Hamiltonian/Manifold.lean`): `IsHamiltonianVectorField`
  ($\iota_X\sigma=df$, the page's sign), `hamiltonianVectorField`,
  `IsNondegenerate.isHamiltonianVectorField_hamiltonianVectorField`,
  `IsNondegenerate.isHamiltonianVectorField_iff_eq` (existence and
  uniqueness), `IsHamiltonianVectorField.apply_eq_of_isMIntegralCurveOn`
  (conservation of $f$), `poissonBracket` with `neg_poissonBracket`,
  `poissonBracket_add_left`, `poissonBracket_const_smul_left` and their right
  versions, `IsNondegenerate.poissonBracket_eq_mvfderiv`
  ($\{f,g\}=df(X_g)$), `IsNondegenerate.mfderiv_hamiltonianVectorField_comp`
  (naturality: $d\chi(X_{g\circ\chi})=X_g\circ\chi$ where $d\chi$ is onto),
  `IsHamiltonianVectorField.mpullback`, `hamiltonianVectorField_add`,
  `hamiltonianVectorField_const_smul`, `contMDiff_hamiltonianVectorField_uncurry`.
  No Leibniz rule for the pointwise product is there.
- **Flows of Hamiltonian fields** (`Geometry/Symplectic/Hamiltonian/CommutingFlow.lean`):
  `IsHamiltonianVectorField.mpullback_flowOf_apply` (local autonomous flows
  are symplectic) and `mpullback_timeDependentFlowOf_of_isHamiltonianVectorField`
  (time-dependent flows with complete suspension are symplectic). The local Moser
  principle `TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_mem`
  (`Geometry/Manifold/DifferentialForm/Flow/Family.lean`) holds along the
  domain of a time-dependent flow without completeness.
- **The energy identity on manifolds**
  (`Geometry/Symplectic/Hamiltonian/ExtendedPhaseSpace/Manifold.lean`):
  `TauCeti.SmoothTwoForm.IsHamiltonianVectorField.hasDerivAt_apply_self_of_hasMFDerivAt`,
  that $u\mapsto H_u(\gamma(u))$ has derivative $(\partial_tH_s)(\gamma(s))$
  at $s$ for any curve with $\gamma'(s)=X_s(\gamma(s))$, hence along
  `timeDependentFlowOf` by `hasMFDerivAt_timeDependentFlowOf`, with no
  completeness; and, in the same file,
  `IsNondegenerate.hasDerivAt_apply_of_hasMFDerivAt` (the rate
  $\partial_tF+\{F,H\}$) and `forall_apply_timeDependentFlowOf_eq_iff`.
- **The Poisson Lie algebra** (`Geometry/Symplectic/Hamiltonian/LieAlgebra.lean`):
  for symplectic `σ`, `σ.PoissonLieAlgebra hσ` (a type synonym of
  `C^∞⟮J, M; ℝ⟯` with the Poisson bracket as Lie bracket), the Lie
  homomorphism `negHamiltonianLieHom hσ` ($f\mapsto -X_f$, a homomorphism for
  Mathlib's bracket), `mem_ker_negHamiltonianLieHom_iff` (its kernel is the
  functions with zero differential) and `range_negHamiltonianLieHom` (its
  range is the ideal `hamiltonianLieIdeal` of Hamiltonian fields).
- **Diffeotopies** (`Geometry/Diffeomorphism/Diffeotopy/`): `TauCeti.Diffeotopy J n M`,
  a level-preserving diffeomorphism of `unitInterval × M`, with `timeSlice`,
  `final`, `cylinderMap` (the motion on `M × unitInterval`), `refl`,
  `trans` (`Φ.trans Ψ` is $\psi_t\circ\phi_t$), `symm`, `transDiffeomorph`
  ($f\circ\phi_t\circ f^{-1}$), `globalFlowDiffeotopy`,
  `compactlySupportedFlowDiffeotopy`, `timeDependentFlowDiffeotopy` and
  `exists_extend_of_isCompact`; and `TauCeti.SmoothForm.isotopyStabilizer`
  (`Stabilizer.lean`). There is no velocity field of a diffeotopy.
- **Hamiltonian diffeotopies** (`Geometry/Symplectic/Flux/Hamiltonian.lean`):
  `TauCeti.Diffeotopy.HasHamiltonian σ Φ F`, for `F : M × unitInterval → ℝ`
  smooth with $\sigma_{\phi_tx}(\partial_t\phi_tx,d\phi_tv)=d(F_t)_x(v)$, the
  Hamiltonian *read along the motion* ($F_t=H_t\circ\phi_t$ for the page's
  $H_t$); `IsHamiltonian` (slices in `diffeomorphStabilizer σ` and some
  `HasHamiltonian`); `HasHamiltonian.trans`, `.symm`, `.transDiffeomorph`,
  `hasHamiltonian_refl`, `hasHamiltonian_globalFlowDiffeotopy`;
  `TauCeti.SmoothForm.hamiltonianGroup σ` with `mem_hamiltonianGroup`,
  `final_mem_hamiltonianGroup`, `hamiltonianGroup_le_isotopyStabilizer`,
  `mul_mul_inv_mem_hamiltonianGroup` and the instance
  `normal_hamiltonianGroup_subgroupOf_diffeomorphStabilizer`.
- **Completeness**: `TauCeti.isCompleteVectorField_timeDependentSuspensionField`
  (`Geometry/Manifold/Flow/TimeDependent.lean`): a jointly `C¹` time-dependent
  field that vanishes off a fixed compact set has complete suspension.
- **Local primitives**: `TauCeti.homotopyOperator` on the cylinder
  `N × unitInterval`, for any manifold `N`, possibly with boundary, with
  `IsSmoothForm.homotopyOperator` and the homotopy formula
  `mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv`
  (`Geometry/Manifold/DifferentialForm/HomotopyOperator.lean`); and
  `mextDeriv_ofFunction_eq_zero_iff` (a function has zero differential
  exactly when it is locally constant).

Missing, and built here: the velocity $X_t$ of a diffeotopy; the criterion
for local flows and for diffeotopies to be symplectic, with the book's
bracket; the Leibniz rule on manifolds; the kernel of
$H\mapsto X_H$ as locally constant functions and the quotient for connected
$M$; the passage between `HasHamiltonian` and the page's $H_t$; Hamiltonians
from exactness, and their uniqueness; and $\mathrm{Ham}_c$.

## Decisions

These settle the questions that `DESIGN.md` leaves to this file.

1. **The velocity $X_t$ is read along the motion.** It is a new definition,
   `TauCeti.Diffeotopy.velocity Φ t`, the smooth vector field
   $y\mapsto\partial_t\phi_t(\phi_t^{-1}y)$, where the time derivative is the
   derivative of `Φ.cylinderMap` along the unit time vector `∂ₜ` below, as
   `HasHamiltonian` and `TauCeti.Diffeotopy.fluxForm` take it. It is defined
   for every $t\in[0,1]$, the ends included (there the derivative is
   one-sided, as for every smooth map on `M × unitInterval`), and it is
   jointly smooth on `unitInterval × M` (`contMDiff_velocity`), so it meets
   the requirement of the endpoint step below. It is not defined through
   the bridge to `TauCeti.eulerianField`: that would need an extension of
   $\Phi$ past both ends and a proof that the choice does not matter. The
   bridge is used only inside the proof of the isotopy criterion.
   - The page's $H_t$ and Tau Ceti's $F$ are related by
     `hasHamiltonian_iff_isHamiltonianVectorField_velocity`:
     `Φ.HasHamiltonian σ F` holds exactly when `F` is smooth and
     `F (Φ.symm (t, ·), t)` has Hamiltonian vector field `Φ.velocity t` for
     every `t`. The milestones are stated with `Φ.velocity` and the page's
     $H_t$; the API of Tau Ceti, read along the motion, is used in the
     proofs.
   - The ordering of the page is translated in the docstrings: the page's
     $\phi_t\circ\psi_t$ is `Ψ.trans Φ`, and its $\chi^{-1}\circ\phi_t\circ\chi$
     is `Φ.transDiffeomorph χ.symm`.
2. **The isotopy criterion** goes through the reading of $\Phi$ over `ℝ`
   that `DESIGN.md` fixes: with $s=$ `Real.smoothTransition`, the family
   $u\mapsto\phi_{s(u)}$ satisfies the hypotheses of Tau Ceti's Eulerian
   theorem, and its Eulerian field at time $u$ is $s'(u)X_{s(u)}$.
   - If every $\phi_t$ preserves $\omega$, so does every $\phi_{s(u)}$, and
     Tau Ceti's theorem makes every $s'(u)\,\iota_{X_{s(u)}}\omega$ closed.
     Each $t\in(0,1)$ is $s(u)$ for some $u\in(0,1)$, where $s'(u)>0$, so
     $\iota_{X_t}\omega$ is closed for $0<t<1$. At $t=0$ and $t=1$ it is
     closed by continuity: $\iota_{X_t}\omega$ is jointly smooth on
     `unitInterval × M`, so its exterior derivative at each point and on
     each pair of vectors is continuous in $t$.
   - Conversely, if every $\iota_{X_t}\omega$ is closed, so is every
     $s'(u)\,\iota_{X_{s(u)}}\omega$; Tau Ceti's theorem makes
     $\phi_{s(u)}^*\omega$ independent of $u$, equal to $\omega$ at $u=0$,
     and $s$ maps $[0,1]$ onto $[0,1]$.
3. **What *Smooth families* provides.** `SymplecticIsotopy.lean` takes from
   `Diffeotopy/Real.lean` the reading of a `Diffeotopy` over `ℝ` by
   `Real.smoothTransition`: its apply lemma, the joint `C^∞` smoothness of
   the family and of its inverses (the two hypotheses of
   `TauCeti.forall_mpullback_eq_iff_forall_mextDeriv_interior_eulerianField_eq_zero`),
   and its Eulerian field, stated pointwise along the motion as
   $X^{\mathbb R}_u(\phi_{s(u)}x)=s'(u)\,\partial_t\phi_t x|_{t=s(u)}$ with
   the time derivative written through `Φ.cylinderMap`, and its form as vector
   fields, `eulerianField_smoothTransitionFamily`, through `velocity`: of this
   part it imports only `Velocity.lean`, for `mfderiv_cylinderMap_time` and
   `velocity`. It also uses that
   `Real.smoothTransition` has positive derivative on $(0,1)$, which the
   review of #420 asks *Smooth families* to plan as a public lemma; if that
   part does not add it, the issue of `SymplecticIsotopy.lean` adds it
   in the namespace `Real.smoothTransition`. `Flux/CompactSupport.lean` takes
   from `ContMDiff/TimeExtension.lean` the extension of a smooth function on
   `unitInterval × M` to `ℝ × M`, and uses that it vanishes at every time at
   a point where the function vanishes at every time, which holds for
   Seeley's formula, a combination of values at the same point; the issue
   of `ContMDiff/TimeExtension.lean` states it as `timeExtend_eq_zero`.
   `PoissonAlgebra.lean` takes nothing from *Smooth families*, and
   `Flux/Hamiltonian.lean` only the merged `DeRham/GoodCover/Basic.lean` and
   `DifferentialForm/SmoothFamily/HomotopyOperator.lean`, and
   `DifferentialForm/SmoothFamily/Poincare.lean` built on them, through
   `DeRham/FamilyPrimitive.lean`.
4. **Hamiltonians from exactness** are built directly, not from the
   smooth-primitive map of `DeRham/SmoothFamily/GoodCover.lean`, which needs a compact
   manifold. Let $\alpha_t=\iota_{X_t}\omega$, a smooth family; the
   Hamiltonian read along the motion is then $F_t\circ\phi_t$, by
   `hasHamiltonian_comp_iff`. Choose a base point in each connected component of $M$ (through
   `ConnectedComponents M`) and let $F_t$ be the primitive of $\alpha_t$
   that vanishes at the base points.
   - *Local step.* Let $U$ be a smoothly contractible chart neighbourhood,
     with contraction $G$. Pull $\alpha$, viewed as a form on
     `unitInterval × U`, back along $((t,x),s)\mapsto(t,G(x,s))$, and apply
     Tau Ceti's `homotopyOperator` on the cylinder over `unitInterval × U`.
     The result is a jointly smooth $P$ with $d(P_t)=\alpha_t$ on $U$: by
     `homotopyOperator_mpullback_prodMap_id_of_isSmoothForm`, $P_t$ is the
     homotopy operator of $G^*\alpha_t$, and `mextDeriv_homotopyOperator`
     needs only that $G^*\alpha_t$ is closed, which holds slice by slice.
     It is the parametric Poincaré lemma of `auxiliary/smooth-primitives.md`
     in degree $1$. The step is the public lemma
     `SymplecticGeometry.IsSmoothlyContractible.exists_contMDiff_mextDeriv_eq_of_forall_mem_closedForms`
     (`DeRham/FamilyPrimitive.lean`), for any parameter manifold.
   - *Gluing.* On $U$, $F_t-P_t$ has zero differential, so
     $F(y,t)=P(y,t)+F(x_0,t)-P(x_0,t)$ for $x_0,y\in U$. The set of points
     $x_0$ for which $t\mapsto F(x_0,t)$ is smooth is therefore open and
     closed in each component, and it contains the base point, where
     $F=0$. So $F$ is jointly smooth.
   This is the path integration of the page's proof route, carried out on
   chart balls. It needs neither compactness nor nondegeneracy.
5. **Uniqueness of the Hamiltonian** is stated in `TauCeti.Diffeotopy`, as
   the review of #420 asks: two Hamiltonians of the same diffeotopy differ
   by `c (ConnectedComponents.mk x) t` for a function `c` smooth in `t`.
   Since $\phi_t$ maps each component to itself, the statement is the same
   for the page's $H_t$ and for Tau Ceti's $F$; both versions are given.
6. **$\mathrm{Ham}_c$** is a subgroup of `M ≃ₘ⟮J, J⟯ M` beside Tau Ceti's
   `hamiltonianGroup`, with the same shape:
   `TauCeti.SmoothForm.compactlySupportedHamiltonianGroup σ`, the final maps
   of the diffeotopies `Φ` with `Φ.IsCompactlySupportedHamiltonian σ`, a new
   predicate in `TauCeti.Diffeotopy`. The predicate asks, as the page does,
   for a Hamiltonian whose page form $H_t$ vanishes off one compact set $K$
   for all $t$; along the motion, `F p = 0` whenever
   `Φ.cylinderMap p ∉ K`. It asks for vanishing off $K$ rather than
   $\operatorname{supp}H_t\subseteq K$ so that `M` need not be Hausdorff;
   in a Hausdorff `M` the two agree. It is not the condition that the
   diffeotopy is compactly supported. On the cylinder $\mathbb{R}\times S^1$
   with $dp\wedge d\theta$, the flow of $H(p,\theta)=f(p)$, with $f=0$ for
   $p\le-1$ and $f=1$ for $p\ge1$, fixes every point with $|p|\ge1$, but by
   uniqueness every Hamiltonian of it is $c(t)$ on one end and $1+c(t)$
   on the other, so none vanishes off a compact set. The group lies in
   `hamiltonianGroup`, is normal in `diffeomorphStabilizer`, and equals
   `hamiltonianGroup` when `M` is compact (with $K=M$). The page's remark that the condition
   guarantees a flow becomes
   `exists_isCompactlySupportedHamiltonian`: a smooth $H$ on
   `M × unitInterval` vanishing off a compact $K$ generates a diffeotopy,
   which fixes every point off $K$. It is the case $\beta=0$ of
   `exists_interior_velocity_eq_add_mextDeriv`, which applies
   `exists_interior_velocity_eq` to the form $\beta+dH$ on
   `unitInterval × M`, for $\beta$ with closed slices vanishing off a
   compact set; `exists_interior_velocity_eq` takes
   `TauCeti.timeDependentFlowDiffeotopy` of the fields
   $(\sigma^\flat)^{-1}\alpha_u$, for an extension $\alpha$ of the form to
   `ℝ × M`, which is complete by
   `isCompleteVectorField_timeDependentSuspensionField`.
7. **The Poisson algebra.** Neither Mathlib nor Tau Ceti has a class of
   Poisson algebras, and `PoissonLieAlgebra` is a type synonym that does
   not carry the pointwise product. The library defines no class: the
   milestone lists the properties (bilinearity and skew-symmetry from Tau
   Ceti's lemmas, Jacobi, and the new Leibniz rule) for functions
   `M → ℝ`, and the Lie structure is Tau Ceti's.
8. **The book's bracket** is `-VectorField.mlieBracket J X Y`, as
   `DESIGN.md`'s table of signs says. The bracket conjunct of the first
   milestone and $[X_F,X_G]_{\mathrm b}=X_{\{F,G\}}$ are stated with it; no
   definition is made for it.
9. **Layout.** `DESIGN.md`'s files are kept, with four more:
   `Geometry/Diffeomorphism/Diffeotopy/Velocity.lean`, for the velocity, which
   concerns diffeotopies and not forms,
   `Geometry/Diffeomorphism/Diffeotopy/Basic.lean`, for facts about
   diffeotopies of any smoothness, at the path of Tau Ceti's file,
   `Geometry/Manifold/Instances/Icc.lean`, for the smoothness of the unit
   vector field of an interval, which concerns intervals only, and
   `Geometry/Manifold/MFDeriv/Prod.lean`, for the derivative of a map on a
   product on `(0, w)` and `(v, 0)`, which concerns products only. Tau Ceti has a
   folder `Geometry/Diffeomorphism/Diffeotopy/` with no `Velocity.lean`. The two
   flux files stay flat in `Geometry/Symplectic/Flux/`: a folder
   `Flux/Hamiltonian/` here would stand beside Tau Ceti's
   `Flux/Hamiltonian.lean`, which the *Principles* of `DESIGN.md` rule out
   so that both trees can move upstream unchanged. The review of #420 notes
   that the two module roots differ, so Lean itself would accept it; the
   principle is about moving upstream.

## Files

Files are under `SymplecticGeometry/`. The declarations are in the
namespaces of the Tau Ceti notions they are about (`TauCeti.Diffeotopy`,
`TauCeti.SmoothTwoForm`, `TauCeti.SmoothForm`), so that they can move into
Tau Ceti unchanged.

| File | Contents |
|---|---|
| `Algebra/Lie/Quotient.lean` | `LieHom.coe_quotKerEquivRange_mk`: the value of `LieHom.quotKerEquivRange` on a class, for `PoissonAlgebra.lean` |
| `Geometry/Manifold/Instances/Icc.lean` | `contMDiff_totalSpaceMk_one_Icc`: the unit vector field `z ↦ 1` of a closed interval is smooth |
| `Geometry/Manifold/MFDeriv/Prod.lean` | `MDifferentiableAt.mfderiv_curry_right_apply`, `MDifferentiableAt.mfderiv_curry_left_apply`: the derivative of a map on a product on `(0, w)` and `(v, 0)` is a partial derivative |
| `Geometry/Diffeomorphism/Diffeotopy/Basic.lean` | `connectedComponent_apply`, `apply_mk_symm_apply`, `symm_apply_mk_apply`: each slice keeps points in their components, and the slices and their inverses cancel in the coerced form `Φ (t, ·)` |
| `Geometry/Diffeomorphism/Diffeotopy/Velocity.lean` | `Diffeotopy.velocity`, its joint smoothness, its value along the motion, its values for `refl` and the flow diffeotopies, and the pullback of $\iota_{X_t}\sigma$ by $\phi_t$ |
| `Geometry/Symplectic/Hamiltonian/PoissonAlgebra.lean` | the Leibniz rule, the local time-dependent flow, the kernel and the quotient, the milestone *Hamiltonian flows and the Poisson algebra* |
| `Geometry/Symplectic/Hamiltonian/SymplecticIsotopy.lean` | symplectic fields and their local flows, the book's bracket, the isotopy criterion, the milestone *Symplectic vector fields and isotopy generators* |
| `Geometry/Manifold/DeRham/FamilyPrimitive.lean` | smooth primitives of a smooth family of one-forms: the local step on a smoothly contractible manifold and the gluing for exact forms on any manifold |
| `Geometry/Symplectic/Flux/Hamiltonian.lean` | the page's $H_t$ beside `HasHamiltonian`, the three rules in the page's form, uniqueness, Hamiltonians from exactness |
| `Geometry/Symplectic/Flux/CompactSupport.lean` | `IsCompactlySupportedHamiltonian`, `compactlySupportedHamiltonianGroup`, the flow of a compactly supported Hamiltonian, the milestone *Hamiltonian isotopies and their composition* |

Imports between the files: `Velocity.lean` imports `Instances/Icc.lean`,
`MFDeriv/Prod.lean` and `Diffeotopy/Basic.lean`;
`SymplecticIsotopy.lean` and
`Flux/Hamiltonian.lean` import `Velocity.lean`; `SymplecticIsotopy.lean`
imports `DifferentialForm/SmoothFamily/Basic.lean` of *Smooth families*, for
`isSmoothFamily_interiorₗ`; `Flux/Hamiltonian.lean`
imports `Diffeotopy/Basic.lean` and `DeRham/FamilyPrimitive.lean`, which
imports `DifferentialForm/SmoothFamily/Poincare.lean` and `DeRham/Map.lean` of *Smooth families*;
`Flux/CompactSupport.lean` imports `Flux/Hamiltonian.lean` and
`SymplecticIsotopy.lean`, and `DifferentialForm/TimeExtension.lean` of
*Smooth families*, for
`TauCeti.Diffeotopy.exists_interior_velocity_eq`. `PoissonAlgebra.lean` imports Tau Ceti,
among it `Hamiltonian/ExtendedPhaseSpace/Manifold.lean` for the energy
identity, `Algebra/Lie/Quotient.lean` for the value of
`LieHom.quotKerEquivRange` on a class, and
`Geometry/Manifold/DifferentialForm/Flow/Family.lean` of
*Contact geometry* for the general flow lemma. `Diffeotopy/Real.lean` of
*Smooth families* imports `Velocity.lean`, for `mfderiv_cylinderMap_time` and
`velocity`. `Diffeotopy/Real.lean` and `Geometry/Manifold/SmoothTransition.lean` of
*Smooth families* import `Instances/Icc.lean`, for
`mdifferentiableAt_subtypeVal_Icc`.

## Definitions and their API

Throughout, `E`, `H`, `J : ModelWithCorners ℝ E H` and `M` with
`[IsManifold J ∞ M]` are as in Tau Ceti's `Flux/Hamiltonian.lean`;
`Φ Ψ : TauCeti.Diffeotopy J ∞ M`, `σ : TauCeti.SmoothTwoForm J M` (which is
`SmoothForm J M ℝ 2`), `I` is `unitInterval`, and `∂ₜ` at `(x, t)` is the tangent
vector `((0 : E), (1 : TangentSpace (𝓡∂ 1) t))` of `M × I`, as in Tau Ceti's
`HasHamiltonian`. Its second component is the interval's unit tangent vector
(Mathlib's `oneTangentSpaceIcc`), which `mfderiv_subtypeVal_Icc_one` sends
to `1` at every `t`. It is not the coordinate vector of the model space:
the chart of the interval at `t = 1` reverses orientation, so that vector
would give `-X₁` there. Further hypotheses are named where they are needed.

### `Geometry/Diffeomorphism/Diffeotopy/Velocity.lean`

- `TauCeti.Diffeotopy.velocity (Φ : Diffeotopy J ∞ M) (t : I) :
  Cₛ^∞⟮J; E, TangentSpace J (M := M)⟯`, the vector field
  `fun y ↦ mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap (Φ.symm (t, y), t) ∂ₜ`.
  API:
  - `velocity_apply` (the body, by `(rfl)` through the coercion of the
    section);
  - `velocity_apply_apply : Φ.velocity t (Φ (t, x)) =
    mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap (x, t) ∂ₜ`, the form used with
    `HasHamiltonian`;
  - `contMDiff_velocity : ContMDiff ((𝓡∂ 1).prod J) J.tangent ∞
    (fun p : I × M ↦ (⟨p.2, Φ.velocity p.1 p.2⟩ : TangentBundle J M))`, from
    Mathlib's `ContMDiff.contMDiff_tangentMap` and
    `contMDiff_totalSpaceMk_one_Icc`; the smoothness of each slice, used
    to build the section, is its composite with `Prod.mk t`;
  - `@[simp] velocity_refl : (refl J ∞ M).velocity t = 0`;
  - `velocity_globalFlowDiffeotopy` (the flow of a complete field `X`, run
    for duration `a`, has velocity `a • X`), from
    `mfderiv_cylinderMap_globalFlowDiffeotopy_time`;
  - `velocity_timeDependentFlowDiffeotopy`, under
    `[FiniteDimensional ℝ E] [BoundarylessManifold J M] [T2Space M]`: the velocity of
    `timeDependentFlowDiffeotopy le_top hX hc` at `t` is `X t`, from
    `hasMFDerivAt_timeDependentFlowOf` (at the ends, the one-sided
    derivative on `I` is the restriction of the derivative on `ℝ`);
  - `mpullback_timeSlice_interior_velocity_apply`: for a two-form `σ`,
    `(φ_t^* ι_{X_t} σ)_x v = (Φ.cylinderMap^* σ)_{(x, t)}(∂ₜ, (v, 0))`, the
    integrand of `fluxForm` and of `HasHamiltonian`.
  - `mfderiv_cylinderMap_time` and `mfderiv_cylinderMap_space`, for
    `Φ : Diffeotopy J n M` with `1 ≤ n`: the motion sends `∂ₜ` at `(x, t)` to
    the velocity of `s ↦ Φ (s, x)` at `t`, and `(v, 0)` to `dφ_t v`.
  The velocities of `trans`, `symm` and `transDiffeomorph` are not needed:
  the three rules come from Tau Ceti's `HasHamiltonian` lemmas through the
  translation of Decision 1.

### `Geometry/Symplectic/Hamiltonian/PoissonAlgebra.lean`

For any two-form `σ`, in the namespace `TauCeti.SmoothTwoForm` like Tau
Ceti's `hamiltonianVectorField_add`, since `X_f` is linear in `df` and
needs neither nondegeneracy nor finite dimension:

- `hamiltonianVectorField_mul`: for `f`, `g` differentiable at `x`,
  `σ.hamiltonianVectorField (f * g) x = f x • σ.hamiltonianVectorField g x +
  g x • σ.hamiltonianVectorField f x`.
- `poissonBracket_mul_left`, `poissonBracket_mul_right` (the Leibniz rule):
  `σ.poissonBracket (f * g) k x = f x * σ.poissonBracket g k x +
  g x * σ.poissonBracket f k x`, and the same in the second slot, for
  differentiable `f`, `g`, from `hamiltonianVectorField_mul`.

In the namespace `TauCeti.SmoothTwoForm`, under the hypotheses of Tau
Ceti's time-dependent flows (`[FiniteDimensional ℝ E] [J.Boundaryless]
[T2Space M]`), for `H : ℝ → M → ℝ` with every `H t` `C²` and `X` jointly
`C²` with `σ.IsHamiltonianVectorField (H t) (X t)` for every `t`:

- `mpullback_timeDependentFlowOf_apply_of_isHamiltonianVectorField`: for
  closed `σ`, `(timeDependentFlowOf X s t)^* σ` equals `σ` at every `x` with
  `((s, t), x) ∈ timeDependentFlowDomain X`; no completeness. Through the
  general `TauCeti.mpullback_timeDependentFlowOf_apply_of_mextDeriv_interior_eq_zero`
  (a closed smooth form whose contractions with every `X t` are closed), the
  case `g = 0`, by Cartan's formula, of
  `mpullback_timeDependentFlowOf_apply_eq_exp_integral_smul_of_mlieDerivForm_eq`,
  in `Geometry/Manifold/DifferentialForm/Flow/Family.lean` of *Contact geometry*. Tau
  Ceti's `mpullback_timeDependentFlowOf_of_isHamiltonianVectorField` is the
  complete case.

For symplectic `σ` (`hσ : σ.IsSymplectic`):

- `mem_ker_negHamiltonianLieHom_iff_isLocallyConstant`: `f` lies in the
  kernel of `negHamiltonianLieHom hσ` exactly when
  `σ.poissonLieAlgebraEquiv hσ f` is locally constant; from
  `mem_ker_negHamiltonianLieHom_iff` and `mextDeriv_ofFunction_eq_zero_iff`.
- `mem_ker_negHamiltonianLieHom_iff_exists_eq_const [PreconnectedSpace M]`:
  the kernel is the constant functions.
- `negHamiltonianLieHomQuotKerEquiv hσ : (σ.PoissonLieAlgebra hσ ⧸
  (σ.negHamiltonianLieHom hσ).ker) ≃ₗ⁅ℝ⁆
  (σ.hamiltonianLieIdeal hσ.isClosed).toLieSubalgebra`, Mathlib's
  `LieHom.quotKerEquivRange` followed by `LieEquiv.ofEq` for the equality
  `range_negHamiltonianLieHom`, with
  `negHamiltonianLieHomQuotKerEquiv_def` and
  `coe_negHamiltonianLieHomQuotKerEquiv_mk` (the class of `f` goes to `-X_f`).
  For connected `M` the quotient is by the constants, by the previous lemma.

### `Geometry/Symplectic/Hamiltonian/SymplecticIsotopy.lean`

- `TauCeti.SmoothTwoForm.mem_symplecticVectorFields_iff_forall_mpullback_flowOf_apply`,
  under `[FiniteDimensional ℝ E] [J.Boundaryless] [T2Space M]` and
  `σ.IsClosed`: a smooth field `X` is symplectic exactly when
  `mpullback J J (flowOf X t) σ x = σ x` at every `(t, x) ∈ flowDomain X`.
  Forward by `mpullback_flowOf_apply_of_mextDeriv_interior_eq_zero`;
  backward because the pullbacks are constant near `t = 0`, so
  `hasDerivAt_mpullback_flowOf_zero` gives $\mathcal L_X\sigma=0$.
- `TauCeti.SmoothTwoForm.isHamiltonianVectorField_neg_mlieBracket`: for
  closed `σ` and `X Y ∈ σ.symplecticVectorFields`, `-mlieBracket J X Y` is a
  Hamiltonian vector field of `fun x ↦ σ (X x) (Y x)` (with `σ` evaluated by
  `SmoothBundleForm.eval₂`), the book's
  $\iota_{[X,Y]_{\mathrm b}}\omega=d(\omega(X,Y))$; from
  `isHamiltonianVectorField_mlieBracket` and skew-symmetry.
- `TauCeti.Diffeotopy.forall_timeSlice_mem_diffeomorphStabilizer_iff`, for
  closed `σ`: `(∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) ↔
  ∀ t, Φ.velocity t ∈ σ.symplecticVectorFields`. Proof as in Decision 2,
  with the endpoint step by `SymplecticGeometry.IsSmoothFamily.ext_on`
  (added to `DifferentialForm/SmoothFamily/Basic.lean`: smooth families
  agreeing on a dense set of parameters agree), applied to the exterior
  derivatives of `SymplecticGeometry.isSmoothFamily_interiorₗ`. It assumes
  `[J.Boundaryless]`, as Tau Ceti's Eulerian theorem does.
- `TauCeti.Diffeotopy.eulerianField_smoothTransitionFamily`, the lemma
  $X^{\mathbb R}_u=s'(u)\,X_{s(u)}$ as vector fields, from the
  pointwise form of Decision 3 and `velocity_apply_apply`; public, in
  `Diffeotopy/Real.lean` of *Smooth families*, after its pointwise form.

### `Geometry/Symplectic/Flux/Hamiltonian.lean`

In `TauCeti.Diffeotopy`, for any two-form `σ` unless said:

- `hasHamiltonian_iff_isHamiltonianVectorField_velocity`:
  `Φ.HasHamiltonian σ F ↔ ContMDiff (J.prod (𝓡∂ 1)) 𝓘(ℝ) ∞ F ∧
  ∀ t, σ.IsHamiltonianVectorField (fun y ↦ F (Φ.symm (t, y), t)) (Φ.velocity t)`,
  from `mpullback_timeSlice_interior_velocity_apply`; and its form with the
  page's Hamiltonian, `hasHamiltonian_comp_iff` (for `G : M × I → ℝ`, the
  function `fun p ↦ G (Φ.cylinderMap p, p.2)` is a Hamiltonian of `Φ`
  exactly when `Φ.IsGeneratedBy σ G`). *`G` generates `Φ`* is the predicate
  `TauCeti.Diffeotopy.IsGeneratedBy σ Φ G`: `G` is smooth and `G (·, t)` has
  Hamiltonian vector field `Φ.velocity t` for every `t`.
- The three rules in the page's form, from `HasHamiltonian.trans`, `.symm`
  and `.transDiffeomorph` through `hasHamiltonian_comp_iff`:
  - `IsGeneratedBy.trans`: if `F` generates `Φ`, `G`
    generates `Ψ` and every slice of `Φ` preserves `σ`, then
    `fun p ↦ F p + G (Φ.symm (p.2, p.1), p.2)` generates `Ψ.trans Φ`
    ($\phi_t\circ\psi_t$ is generated by $F_t+G_t\circ\phi_t^{-1}$);
  - `IsGeneratedBy.symm`: if `F` generates `Φ` and every
    slice preserves `σ`, then `fun p ↦ -F (Φ.cylinderMap p, p.2)` generates
    `Φ.symm`;
  - `IsGeneratedBy.transDiffeomorph`: for
    `χ ∈ diffeomorphStabilizer σ`, if `F` generates `Φ` then
    `fun p ↦ F (χ p.1, p.2)` generates `Φ.transDiffeomorph χ.symm`
    ($\chi^{-1}\circ\phi_t\circ\chi$ is generated by $F_t\circ\chi$).
- Uniqueness: `HasHamiltonian.exists_sub_eq` (for `F`, `G` Hamiltonians of
  the same `Φ`, there is `c : ConnectedComponents M → I → ℝ`, each `c i`
  smooth, with `F p - G p = c (ConnectedComponents.mk p.1) p.2`), from
  `MDifferentiable.isLocallyConstant_of_mfderiv_eq_zero`; and
  `IsGeneratedBy.exists_sub_eq`, the same for two functions that generate
  `Φ` in the page's form, using that `Φ (t, x)` lies in the component of
  `x`.
- `isHamiltonian_iff_forall_interiorₗ_velocity_mem_exactForms`: if every
  slice of `Φ` preserves `σ`, then `Φ.IsHamiltonian σ ↔
  ∀ t, σ.interiorₗ (Φ.velocity t) ∈ exactForms J M 1`. The backward
  direction builds the Hamiltonian as in Decision 4, with
  `exists_hasHamiltonian_of_forall_mem_exactForms` as the public
  statement; the local step is the public lemma
  `SymplecticGeometry.IsSmoothlyContractible.exists_contMDiff_mextDeriv_eq_of_forall_mem_closedForms`
  of `DeRham/FamilyPrimitive.lean`, for a smooth family of closed
  one-forms on a smoothly contractible manifold, over any parameter
  manifold.
- The gluing of Decision 4 is a public lemma, in the namespace
  `SymplecticGeometry` since its hypothesis is the library's
  `IsSmoothFamily`, in `Geometry/Manifold/DeRham/FamilyPrimitive.lean`,
  for any manifold `M` (no compactness, no form `σ`) and any parameter
  manifold `N`, because *Isotopy extension* applies it on open subsets
  (its `Cohomological/Primitive.lean`). This is what *Isotopy extension*
  uses:

  ```lean
  theorem SymplecticGeometry.exists_contMDiff_mextDeriv_eq_of_forall_mem_exactForms
      {α : N → SmoothForm I M ℝ 1} (hα : IsSmoothFamily K α)
      (hex : ∀ t, α t ∈ exactForms I M 1) :
      ∃ f : N × M → ℝ, ContMDiff (K.prod I) 𝓘(ℝ) ∞ f ∧
        ∀ t, mextDeriv (RoughForm.ofFunction I fun x ↦ f (t, x)) =
          (α t : RoughForm I M ℝ 1)
  ```

  It is the family version of Tau Ceti's
  `exists_contMDiff_mextDeriv_eq_of_mem_exactForms`, and
  `exists_hasHamiltonian_of_forall_mem_exactForms` applies it to
  $\alpha_t=\iota_{X_t}\sigma$ over `unitInterval`. The parameter comes
  first, as in *Smooth families*.

### `Geometry/Symplectic/Flux/CompactSupport.lean`

- `TauCeti.Diffeotopy.IsCompactlySupportedHamiltonian (σ) (Φ) : Prop`:
  every slice preserves `σ`, and there are `F` with `Φ.HasHamiltonian σ F`
  and a compact `K` with `F p = 0` whenever `Φ.cylinderMap p ∉ K`. API:
  `isCompactlySupportedHamiltonian_iff` (the body),
  `IsCompactlySupportedHamiltonian.isHamiltonian`,
  `isCompactlySupportedHamiltonian_refl`, `.trans`, `.symm` and
  `.transDiffeomorph` (for `f ∈ diffeomorphStabilizer σ`), with the compact
  sets `K_Ψ ∪ Ψ.cylinderMap '' (K_Φ ×ˢ univ)`, the image of `K` under the
  inverse motion, and `f '' K`, all compact as continuous images; and
  `isCompactlySupportedHamiltonian_of_compactSpace` (on a compact `M`, every
  Hamiltonian diffeotopy, with `K = univ`).
- `TauCeti.SmoothForm.compactlySupportedHamiltonianGroup σ :
  Subgroup (M ≃ₘ⟮J, J⟯ M)`, defined like `hamiltonianGroup`, with
  `mem_compactlySupportedHamiltonianGroup`,
  `final_mem_compactlySupportedHamiltonianGroup`,
  `compactlySupportedHamiltonianGroup_le_hamiltonianGroup`,
  `mul_mul_inv_mem_compactlySupportedHamiltonianGroup`, the instance
  `normal_compactlySupportedHamiltonianGroup_subgroupOf_diffeomorphStabilizer`,
  and `compactlySupportedHamiltonianGroup_eq_hamiltonianGroup [CompactSpace M]`.
- `TauCeti.Diffeotopy.exists_interior_velocity_eq`, under the same instances
  and `hσ`, added by *Isotopy extension*: for a smooth one-form `Ω` on
  `unitInterval × M` whose slices `Ω_t` are closed and vanish off a compact
  `L`, there is `Φ` with `ι_{Φ.velocity t} σ = Ω_t`, every slice in
  `diffeomorphStabilizer σ`, and `Φ (t, y) = y` for `y ∉ L`. Trajectories
  need no conjunct here: for every diffeotopy, a curve whose derivative is
  `Φ.velocity` is the trajectory of its start, by
  `TauCeti.Diffeotopy.apply_eq_of_mfderiv_eq_velocity`.
- `TauCeti.Diffeotopy.exists_isCompactlySupportedHamiltonian`, under
  `[FiniteDimensional ℝ E] [J.Boundaryless] [T2Space M]` and
  `hσ : σ.IsSymplectic`: for `G : M × I → ℝ` smooth and `K` compact with
  `G p = 0` whenever `p.1 ∉ K`, there is `Φ` such that `G` generates `Φ`,
  `Φ.IsCompactlySupportedHamiltonian σ`, and `Φ (t, x) = x` for `x ∉ K`.
  Proof as in Decision 6: `exists_interior_velocity_eq_add_mextDeriv` for
  `β = 0`, and
  `isHamiltonianVectorField_iff_interior_eq`. It is also the example of the
  new predicate.

## Main results

The three milestones, each one theorem that collects the results above. Each
docstring ends with the milestone line, and translates Tau Ceti's objects to
the page's: `Φ.velocity t` is $X_t$, `-mlieBracket` is the book's bracket,
`negHamiltonianLieHom` is $-(H\mapsto X_H)$, and the ordering of
compositions is as in Decision 1.

- `TauCeti.SmoothTwoForm.IsSymplectic.symplecticVectorFields_and_isotopies`
  (`SymplecticIsotopy.lean`), under `[FiniteDimensional ℝ E]
  [J.Boundaryless] [T2Space M]` and `hσ : σ.IsSymplectic`: for every smooth
  field `X`, `X ∈ σ.symplecticVectorFields ↔ mlieDerivForm X σ = 0` and
  `X ∈ σ.symplecticVectorFields ↔ ∀ (t, x) ∈ flowDomain X, (flowOf X t)^* σ
  = σ` at `x`; for every diffeotopy `Φ`, the criterion
  `forall_timeSlice_mem_diffeomorphStabilizer_iff`; and for symplectic `X`,
  `Y`, `isHamiltonianVectorField_neg_mlieBracket`. The milestone needs no
  compactness, as the page says: the isotopy is given. Milestone:
  *Symplectic vector fields and isotopy generators*.
- `TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlow_and_poissonAlgebra`
  (`PoissonAlgebra.lean`), under the same hypotheses: for every smooth `H`,
  `σ.IsHamiltonianVectorField H (σ.hamiltonianVectorField H)` and uniqueness
  (`isHamiltonianVectorField_iff_eq`); the local autonomous flow preserves
  `σ` and `H` on its domain (Tau Ceti's `mpullback_flowOf_apply` and
  `IsFirstIntegral.apply_maximalIntegralCurve`); the local time-dependent
  flow preserves `σ` and satisfies the energy identity (Tau Ceti's
  `(hX t).hasDerivAt_apply_self_of_hasMFDerivAt hH
  (hasMFDerivAt_timeDependentFlowOf …)`); the bracket is bilinear,
  skew-symmetric, and satisfies Jacobi and Leibniz, on smooth functions, and
  the bracket of two smooth functions is smooth (Tau Ceti's
  `IsNondegenerate.contMDiff_poissonBracket`);
  `σ.hamiltonianVectorField (σ.poissonBracket F G) = -mlieBracket J X_F X_G`;
  naturality for `χ ∈ diffeomorphStabilizer σ`, as
  `mfderiv J J χ q (σ.hamiltonianVectorField (H ∘ χ) q) =
  σ.hamiltonianVectorField H (χ q)` (the page's
  $X_{H\circ\chi}=\chi^*X_H$ with $d\chi_q$ applied to both sides); the
  kernel of `negHamiltonianLieHom hσ` is the locally constant functions;
  for `[PreconnectedSpace M]` it is the constants; and
  `negHamiltonianLieHomQuotKerEquiv hσ` identifies the quotient with the
  Hamiltonian fields. Milestone: *Hamiltonian flows and the Poisson
  algebra*.
- `TauCeti.SmoothTwoForm.IsSymplectic.isHamiltonian_iff_and_normal_hamiltonianGroup`
  (`Flux/CompactSupport.lean`), under the same hypotheses: for `Φ` whose
  slices preserve `σ`, `Φ.IsHamiltonian σ ↔ ∀ t, σ.interiorₗ (Φ.velocity t) ∈
  exactForms J M 1` and `Φ.IsHamiltonian σ ↔ ∃ G` generating `Φ`; two
  generating functions differ by a function of time on each component; the
  three rules; `hamiltonianGroup σ ≤ diffeomorphStabilizer σ` and
  `((hamiltonianGroup σ).subgroupOf (diffeomorphStabilizer σ)).Normal`;
  `isCompactlySupportedHamiltonian_iff_isGeneratedBy` and
  `exists_isCompactlySupportedHamiltonian`;
  `compactlySupportedHamiltonianGroup_le_hamiltonianGroup`,
  `((compactlySupportedHamiltonianGroup σ).subgroupOf
  (diffeomorphStabilizer σ)).Normal`; and, for `[CompactSpace M]`,
  `compactlySupportedHamiltonianGroup σ = hamiltonianGroup σ`. Milestone:
  *Hamiltonian isotopies and their composition*.

The milestones hold in the page's form and generality: no compactness except
where the page assumes it, any dimension (for `M` empty or of dimension $0$
every statement holds trivially), and `σ` only closed where the page's
argument uses no more (Decisions 4 and 5 use neither closedness nor
nondegeneracy). The boundaryless and Hausdorff hypotheses are those of Tau
Ceti's flows, which `DESIGN.md` allows. No entry in `ERRATA.md` is needed:
the page's statements are correct as read here, and the correction of
Exercise 3.1.8 that it cites concerns only a proof route of the Jacobi
identity, which Tau Ceti proves (`IsNondegenerate.poissonBracket_jacobi`).

## What it uses

- From *Smooth families*: `Diffeotopy/Real.lean` (the reading of a `Diffeotopy`
  over `ℝ`, Decision 3) for `SymplecticIsotopy.lean`, and
  `ContMDiff/TimeExtension.lean` (the extension in time, Decision 3) for
  `Flux/CompactSupport.lean`, and the merged `DeRham/GoodCover/Basic.lean`
  (smoothly contractible manifolds) and
  `DifferentialForm/SmoothFamily/HomotopyOperator.lean` (the homotopy operator
  on smooth families of forms, `IsSmoothFamily.homotopyOperator`, and through
  `DifferentialForm/HomotopyOperator.lean` the primitive of a closed form
  given by a contraction), through
  `DifferentialForm/SmoothFamily/Poincare.lean` (the parametric Poincaré
  lemma, `IsSmoothlyContractible.exists_isSmoothFamily_mextDerivₗ_eq`), for
  `DeRham/FamilyPrimitive.lean`.
  `Velocity.lean` (with `Instances/Icc.lean`) uses only Mathlib and Tau Ceti.
- From *Contact geometry*: `Geometry/Manifold/DifferentialForm/Flow/Family.lean`
  (the general flow lemma) for `PoissonAlgebra.lean`.
- From *Liouville structures*: `Geometry/Manifold/MFDeriv/Opens.lean`
  (`mdifferentiable_subtypeVal`) for `DeRham/FamilyPrimitive.lean`.
- From Tau Ceti: the declarations of *What there is*.
- From Mathlib: `VectorField.mlieBracket`, `ContMDiff.contMDiff_tangentMap`,
  `LieHom.quotKerEquivRange`, `LieEquiv.ofEq`,
  `ConnectedComponents`, `Real.smoothTransition`.

## Building issues

Each is a few hundred lines; each is blocked by the issues it names.

1. **The velocity of a diffeotopy.** `Velocity.lean`, all of it, and
   `Instances/Icc.lean`. About 250
   lines. No blockers.
2. **The Poisson algebra on a symplectic manifold.** `PoissonAlgebra.lean`,
   with its milestone. About 350 lines. No blockers.
3. **Symplectic isotopies.** `SymplecticIsotopy.lean`, with its milestone.
   About 300 lines. Blocked by 1 and by the issue of *Smooth families* that
   builds `Diffeotopy/Real.lean` (#467 until it is split).
4. **Hamiltonians of a diffeotopy in the page's form.** In
   `Flux/Hamiltonian.lean`: `hasHamiltonian_iff_isHamiltonianVectorField_velocity`,
   `hasHamiltonian_comp_iff`, the three rules and the uniqueness lemmas.
   About 250 lines. Blocked by 1.
5. **Hamiltonians from exactness.** In `DeRham/FamilyPrimitive.lean` and
   `Flux/Hamiltonian.lean`: the local
   step, the gluing (`exists_contMDiff_mextDeriv_eq_of_forall_mem_exactForms`),
   `exists_hasHamiltonian_of_forall_mem_exactForms` and
   `isHamiltonian_iff_forall_interiorₗ_velocity_mem_exactForms`. About 350
   lines. Blocked by 4.
6. **Compactly supported Hamiltonian diffeomorphisms.**
   `Flux/CompactSupport.lean`: the predicate and the group with their API,
   and the equality on compact manifolds. About 250 lines. Blocked by 4.
7. **The flow of a compactly supported Hamiltonian, and the milestone.** In
   `Flux/CompactSupport.lean`: `exists_isCompactlySupportedHamiltonian` and
   the milestone *Hamiltonian isotopies and their composition*. About 250
   lines. Blocked by 5, 6 and the issue of *Smooth families* that builds
   `ContMDiff/TimeExtension.lean` (#467 until it is split).

Issues 1 and 2 can start at once, 4 and 6 after 1, and 5 after 4; only 3
and 7 wait for *Smooth families*.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §3.1: Proposition 3.1.5, Remark 3.1.6, Exercise 3.1.8, Proposition 3.1.10
  and the discussion after it, Definition 3.1.13, Exercise 3.1.14,
  Remark 3.1.15.
* [D. McDuff and D. Salamon, errata to the third edition][McDuffSalamon2019Errata],
  the correction to p. 100 (Exercise 3.1.8).
* R. T. Seeley, *Extension of C^∞ functions defined in a half space*,
  Proc. Amer. Math. Soc. 15 (1964), 625–626, for the time extension that
  issue 7 uses through `ContMDiff/TimeExtension.lean`.
