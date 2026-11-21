# Linear complex structures

The detailed design of part 8 of `DESIGN.md`, *Linear complex structures*. It
proves the milestone *Linear complex structures are standard* of
`atlas/linear-symplectic-geometry.md`, following McDuff–Salamon
[McDuffSalamon2017], Propositions 2.5.1 and 2.5.2.

All declarations of Tau Ceti and Mathlib named below were checked against the
pinned versions (Tau Ceti `v4.37.0-rc1`, see `lakefile.toml`). Paths of Tau
Ceti files are relative to `.lake/packages/TauCeti/TauCeti/`.

## What there is, and what is missing

The space of all linear complex structures on $V$ is Tau Ceti's type
`TauCeti.AlmostComplexStructure V`, with the topology of
`Geometry/Symplectic/AlmostComplex/Topology.lean`, induced by the operator norm
(`isEmbedding_toContinuousLinearMap`, `continuous_iff`). `DESIGN.md` fixes that
the library never uses another model; matrices with square $-1$ appear only
through a homeomorphism with it.

Already proved:

- the adapted basis $(v_1,Jv_1,\dots,v_n,Jv_n)$,
  `TauCeti.AlmostComplexStructure.exists_basis_apply_one_eq`, and, closer to
  what we need, `TauCeti.AlmostComplexStructure.exists_linearEquiv_I_smul`
  (`Geometry/Symplectic/Finrank.lean`): for any finite-dimensional complex
  space $G$ with $\dim_{\mathbb{R}}V=2\dim_{\mathbb{C}}G$ there is a real
  isomorphism $\varphi:G\to V$ with $\varphi(iz)=J\varphi(z)$;
- transport of a complex structure along a linear equivalence,
  `AlmostComplexStructure.transport`, with `transport_apply`, `transport_trans`,
  `transport_symm_transport` (`Geometry/Symplectic/Transport.lean`);
- the stabilizer of $J_0$ in matrices,
  `Matrix.GeneralLinearGroup.mem_range_realify_iff`
  (`LinearAlgebra/Matrix/GeneralLinearGroup/Symplectic/Unitary.lean`), and in
  orthogonal matrices, `Matrix.orthogonalGroup_inf_centralizer_J`; the
  determinant of a realification, `Matrix.det_realify` ($=|\det|^2$);
- the matrix of a continuous automorphism of Euclidean space,
  `Matrix.GeneralLinearGroup.ofEuclideanCLE`, a group isomorphism with inverse
  `Matrix.toEuclideanCLE`, both continuous in families
  (`Analysis/Matrix/EuclideanLin.lean`);
- the open mapping theorem for group actions, Mathlib's
  `isOpenMap_smul_of_sigmaCompact` (`Mathlib/Topology/Algebra/Group/OpenMapping.lean`):
  for a σ-compact group acting continuously and transitively on a Hausdorff
  Baire space, every orbit map is open; Tau Ceti's `Units.instSigmaCompactSpace`
  (`Topology/Algebra/Group/Units.lean`), with its instance
  `SigmaCompactSpace (Matrix m n α)` (`Topology/Instances/Matrix.lean`), makes
  `GL n ℝ` σ-compact;
- the orbit–stabilizer homeomorphism for a compact quotient,
  `TauCeti.quotientStabilizerHomeomorph`
  (`Topology/Algebra/GroupAction/Transitive.lean`), and the algebraic
  `TauCeti.quotientStabilizerEquiv`;
- the polar deformation `Matrix.GeneralLinearGroup.polarDeformation A t`
  $=P^{1-t}U$ for $A=PU$, $P=\sqrt{AA^*}$, with `polarDeformation_zero`,
  `polarDeformation_one`, `polarDeformation_toUnits` (it fixes unitary
  matrices) and `polarHomotopy` (`Analysis/Matrix/Polar/Deformation.lean`);
  `CFC.rpow_unitary_mul_mul_star` (unitary conjugation commutes with real
  powers);
- `TauCeti.Matrix.instPathConnectedSpaceSpecialOrthogonalGroup`, and the
  instances `CompactSpace` and `IsTopologicalGroup` for
  `Matrix.specialUnitaryGroup n 𝕜` (so for `Matrix.specialOrthogonalGroup`,
  an `abbrev` of it over `ℝ`) in `Topology/Algebra/UnitaryGroup.lean`;
- orthogonal complex structures: `exists_adapted_orthonormalBasis`
  (an orthonormal basis $(u_1,Ju_1,\dots)$ when $\|Jv\|=\|v\|$), and in
  dimension four `exists_unitary_orthonormalBasis_of_norm_eq_one` and
  `toBasis_orientation_eq_symplecticForm_orientation_four`
  (`Geometry/Symplectic/Complex/OrthonormalBasis.lean`);
- `TauCeti.SymplecticForm.orientation` and
  `TauCeti.SymplecticForm.Tames.orientation_reindex`
  (`Geometry/Symplectic/Orientation.lean`): every $J$-adapted basis of a
  structure tamed by $\omega$ induces the symplectic orientation of $\omega$;
- `ContinuousMap.HomotopyEquiv.ofDeformationRetraction`, and its variants
  `ofWeakDeformationRetraction` (the homotopy runs inside a larger subspace)
  and `ofRetraction` (`Topology/Homotopy/DeformationRetract.lean`);
- for $\mathbb{R}^4$: Mathlib's `Quaternion.linearIsometryEquivTuple :
  ℍ[ℝ] ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)` (`Mathlib/Analysis/Quaternion.lean`)
  and `LinearIsometryEquiv.piLpCongrLeft`
  (`Mathlib/Analysis/Normed/Lp/PiLp.lean`).

Missing, and built here: the isomorphism $\Phi$ packaged with the model
`StdSpace ι`; the action of $\mathrm{GL}(2n,\mathbb{R})$ on complex structures;
the homeomorphism with the quotient; the orientation condition and the two
components; the homotopy type of the component of $J_0$; and the case
$\mathbb{R}^4$.

## Decisions

These settle the questions that `DESIGN.md` leaves to this file.

1. **The conjugating isomorphism** comes from Tau Ceti's
   `exists_linearEquiv_I_smul` with $G=$ `ι → ℂ`, composed with
   `complexToRealEuclidean ι`. This needs no norm on $V$ and works for any
   finite index type `ι`, so it replaces the route through
   `exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul` that
   `DESIGN.md` mentions, whose dimension is only existential.
2. **The quotient homeomorphism** is obtained from the open mapping theorem
   for group actions, not from a local section or the inverse function
   theorem. The orbit map $g\mapsto g\cdot J_0$ is continuous, surjective and,
   by `isOpenMap_smul_of_sigmaCompact`, open; so the induced continuous
   bijection from the quotient is open, hence a homeomorphism. Its hypotheses
   hold: `GL (ι ⊕ ι) ℝ` is σ-compact, and the space of complex structures is
   closed in the finite-dimensional space of operators (the condition
   $J^2=-1$), so it is locally compact and Hausdorff, hence Baire. The general
   statement goes into a file of its own, at the path of Tau Ceti's compact
   version so that it can move there, with its name in the namespace
   `MulAction` rather than `TauCeti`.
3. **The model of GL(2n,ℝ)/GL(n,ℂ)** is
   Mathlib's quotient `GL (ι ⊕ ι) ℝ ⧸ (Matrix.GeneralLinearGroup.realify ι ℂ).range`
   by the realified group, with its quotient topology.
4. **The model of $\mathrm{SO}(2n)/\mathrm{U}(n)$** is Mathlib's quotient
   `specialOrthogonalGroup (ι ⊕ ι) ℝ ⧸ MulAction.stabilizer _ (stdComplexStructure ι)`,
   and a lemma identifies the stabilizer with the realified unitary group; the
   milestone states that identification as a conjunct of its own. The
   space of complex structures compatible with the Euclidean metric (the
   orthogonal ones) is the bridge: it is a deformation retract of all complex
   structures, and its positive part is homeomorphic to that quotient. No
   homotopy theory of fibrations is needed, which is the advantage over the
   book's sketch (the quotients
   $\mathrm{GL}^+(2n)/\mathrm{GL}(n,\mathbb{C})$ and
   $\mathrm{SO}(2n)/\mathrm{U}(n)$ are compared through explicit maps).
5. **The deformation retraction** is the polar deformation of the matrix of
   $J$: $J_t=P^{-t}J$ with $P=\sqrt{JJ^{T}}$, which is Tau Ceti's
   `polarDeformation` of the matrix of $J$. It stays among complex structures:
   writing $J=PU$ with $U$ orthogonal, $J^{-1}=-J$ gives
   $(JJ^T)^{-1}=J^TJ$, so $U^{-1}P^2U=P^{-2}$; by
   `CFC.rpow_unitary_mul_mul_star`, $UP^{s}U^{-1}=P^{-s}$ for all real $s$,
   hence $(P^{1-t}U)^2=U^2=J^2=-1$. The conjugation step uses nothing about
   matrices: it holds for a unit $a$ with $a^2=-1$ in any C⋆-algebra, and is
   stated in that generality. It fixes the orthogonal structures
   (`polarDeformation_toUnits`) and ends at the orthogonal factor $U$.
6. **The orientation condition.** A complex structure on `StdSpace ι` is
   *positively oriented* if it lies in the orbit of $J_0$ under the matrices
   of positive determinant (Mathlib's `Matrix.GLPos`). A theorem shows that
   this is the book's condition: the adapted bases of $J$ induce the standard
   orientation, which is the symplectic orientation of $\omega_0$ (Tau Ceti's
   `(stdForm ι).orientation`, the orientation of the bases
   $(x_1,y_1,\dots,x_n,y_n)$; the coordinate order
   $(x_1,\dots,x_n,y_1,\dots,y_n)$ differs from it by the sign
   $(-1)^{n(n-1)/2}$, so it would not contain $J_0$ for $n=2$).
7. **The model of $S^2$** is `Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`.
   The explicit map for $n=2$ uses quaternions: identify `StdSpace (Fin 2)`
   with Mathlib's `ℍ[ℝ]` by the linear isometry sending $z$ to
   $x_1+y_1i+x_2j+y_2k$ (so $J_0$ is left multiplication by $i$), assembled
   from Mathlib's isometries rather than proved from this formula. A unit
   vector $u\in S^2$ gives the complex structure "left multiplication by the
   pure quaternion $u_0i+u_1j+u_2k$"; conversely an orthogonal positively
   oriented $J$ gives the imaginary part of $J(1)$. These are inverse
   homeomorphisms between $S^2$ and the orthogonal positively oriented
   structures, and the retraction of decision 5 gives the homotopy
   equivalence.
8. **Dimension zero.** For `ι` empty there is exactly one complex structure
   (the zero map of the zero space), so the space of complex structures is
   connected, not a union of two components. The statement about two
   components is made for `Nonempty ι`, and `ERRATA.md` records this; the
   other statements hold for all `ι`.

## Files

Files are under `SymplecticGeometry/`. `DESIGN.md` lists three files for this
part; this design keeps them and adds six, each with the topic its path says:
the actions on complex structures, their general topology, the general
orbit–stabilizer homeomorphism, the conjugation identity for units of square
$-1$, the polar deformation of matrices of square $-1$, and the orthogonal
complex structures. The first two are stated for any space, since
*Compatible complex structures* uses them too.

| File | Contents |
|---|---|
| `LinearAlgebra/ComplexStructure/Action.lean` | the action of `V ≃ₗ[ℝ] V`, and of `GL n ℝ` and `specialOrthogonalGroup n ℝ` on the structures of `EuclideanSpace ℝ n` |
| `Topology/ComplexStructure/Basic.lean` | the closed embedding into operators, `T2Space` and `LocallyCompactSpace`, for finite-dimensional normed `V`; the matrix homeomorphism and continuity of the actions, for `EuclideanSpace ℝ n` |
| `LinearAlgebra/ComplexStructure/Standard.lean` | the isomorphism $\Phi$, transitivity, the stabilizer, positively oriented structures |
| `Topology/Algebra/GroupAction/Transitive.lean` | the orbit–stabilizer homeomorphism for σ-compact groups |
| `Topology/ComplexStructure/Orbit.lean` | the space as GL(2n,ℝ)/GL(n,ℂ), the positively oriented structures form a clopen set |
| `Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Polar.lean` | the polar unitary factor of a unit of square $-1$ inverts the powers of its positive factor |
| `Analysis/Matrix/Polar/Deformation.lean` | the polar deformation preserves square $-1$ |
| `Topology/ComplexStructure/Orthogonal.lean` | the orthogonal complex structures, the deformation retraction onto them |
| `Topology/ComplexStructure/Oriented.lean` | the stabilizer of $J_0$ in $\mathrm{SO}(2n)$, the component of $J_0$, the two components, the homotopy type $\mathrm{SO}(2n)/\mathrm{U}(n)$, the case $\mathbb{R}^4$, the milestone |

## Definitions and their API

Below, `V` is a real vector space, `n` and `ι` finite types with decidable
equality, and `J₀ = stdComplexStructure ι` (from *Standard model*). The
actions are stated where no evenness is needed, for `GL n ℝ` and
`EuclideanSpace ℝ n`; `ι ⊕ ι` appears only together with $J_0$.

### `LinearAlgebra/ComplexStructure/Action.lean`

Declarations about Tau Ceti's type go in its namespace
`TauCeti.AlmostComplexStructure`, as `AGENTS.md` asks.

- `instance instMulActionLinearEquiv :
  MulAction (V ≃ₗ[ℝ] V) (AlmostComplexStructure V)`, `e • J = J.transport e`,
  for any `[AddCommGroup V] [Module ℝ V]`; with `smul_def` (by `(rfl)`),
  `@[simp] smul_apply : (e • J) v = e (J (e.symm v))`, and
  `@[simp] toLinearMap_smul`. The axioms are `transport_refl` and
  `transport_trans`. *Compatible complex structures* states the equivariance
  of $J_{g,\omega}$ with it.
- `instance instMulActionGeneralLinearGroup :
  MulAction (GL n ℝ) (AlmostComplexStructure (EuclideanSpace ℝ n))`, the
  action of matrices,
  `g • J = J.transport ((g : Matrix _ _ ℝ).toEuclideanCLE g.det_ne_zero).toLinearEquiv`;
  built as `MulAction.compHom` of the previous action along
  `Matrix.GeneralLinearGroup.ofEuclideanCLE.symm` followed by forgetting
  continuity. API: `generalLinearGroup_smul_def` (the formula above; not
  `(rfl)`, since Tau Ceti does not expose the body of `ofEuclideanCLE`),
  `@[simp] generalLinearGroup_smul_apply :
  (g • J) v = Matrix.toEuclideanLin g (J (Matrix.toEuclideanLin ↑g⁻¹ v))` and
  `@[simp] toLinearMap_generalLinearGroup_smul :
  (g • J).toLinearMap = toEuclideanLin g ∘ₗ J.toLinearMap ∘ₗ toEuclideanLin ↑g⁻¹`.
- `isComplexLinearMap_self_iff_commute :
  IsComplexLinearMap J J f ↔ Commute f J.toLinearMap`, for
  `f : Module.End ℝ V`, and `transport_eq_transport_iff`: for any `J` and
  `Φ Ψ : V ≃ₗ[ℝ] W`, `J.transport Φ = J.transport Ψ` if and only if
  `Φ ≪≫ₗ Ψ.symm` is complex linear for `J`.
- `instance instMulActionSpecialOrthogonalGroup :
  MulAction (specialOrthogonalGroup n ℝ) (AlmostComplexStructure (EuclideanSpace ℝ n))`,
  `MulAction.compHom` of the matrix action along the inclusion
  `Unitary.toUnits.comp (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup)`
  into `GL n ℝ` (no new name for that homomorphism). It has no apply lemma of
  its own: `@[simp] specialOrthogonalGroup_smul_def` rewrites `g • J` as the
  action of that unit, so `generalLinearGroup_smul_apply` serves both actions.

### `Topology/ComplexStructure/Basic.lean`

- `TauCeti.AlmostComplexStructure.isClosedEmbedding_toContinuousLinearMap`
  (for finite-dimensional normed `V`: the condition $J^2=-1$ is closed), and
  the instances `T2Space` and `LocallyCompactSpace` on
  `AlmostComplexStructure V`; Mathlib then gives `BaireSpace`.
- `TauCeti.AlmostComplexStructure.homeomorphMatrix n :
  AlmostComplexStructure (EuclideanSpace ℝ n) ≃ₜ {A : Matrix n n ℝ // A * A = -1}`,
  sending `J` to `Matrix.toEuclideanCLM.symm` of its operator, with `@[simp]`
  lemmas `homeomorphMatrix_apply_coe` and `homeomorphMatrix_symm_apply_apply`.
  Later files compute with matrices through it, as `DESIGN.md` requires.
- `instance : ContinuousSMul (GL n ℝ) (AlmostComplexStructure (EuclideanSpace ℝ n))`
  (the matrix of `g • J` is $gJg^{-1}$), and from it the `ContinuousSMul`
  instance of `specialOrthogonalGroup n ℝ`.

### `LinearAlgebra/ComplexStructure/Standard.lean`

*Positively oriented structures.*

- `def IsPositivelyOriented (J : AlmostComplexStructure (StdSpace ι)) : Prop :=
  ∃ g ∈ Matrix.GLPos (ι ⊕ ι) ℝ, g • J₀ = J`, in `SymplecticGeometry`. API:
  `isPositivelyOriented_def` (by `(rfl)`);
  `@[simp] isPositivelyOriented_stdComplexStructure`;
  `IsPositivelyOriented.smul (hJ) (hg : 0 < (g : Matrix _ _ ℝ).det)`;
  `isPositivelyOriented_smul_stdComplexStructure_iff :
  IsPositivelyOriented (g • J₀) ↔ 0 < (g : Matrix _ _ ℝ).det` (the hard
  direction: two such `g` differ by an element of the stabilizer, a
  realification, whose determinant is $|\det|^2>0$ by `Matrix.det_realify`);
  `isPositivelyOriented_transport_iff (Φ : StdSpace ι ≃ₗ[ℝ] StdSpace ι) :
  IsPositivelyOriented (J₀.transport Φ) ↔ 0 < LinearMap.det (Φ : _ →ₗ[ℝ] _)`;
  `exists_not_isPositivelyOriented [Nonempty ι]` (the transport of $J_0$ by the
  reflection $x_1\mapsto-x_1$); and the orientation characterization below.

### `Topology/Algebra/GroupAction/Transitive.lean`

- `MulAction.quotientStabilizerHomeomorphOfSigmaCompact (b : X) :
  G ⧸ MulAction.stabilizer G b ≃ₜ X`, under the hypotheses of
  `isOpenMap_smul_of_sigmaCompact` (`[IsTopologicalGroup G]
  [SigmaCompactSpace G] [BaireSpace X] [T2Space X] [ContinuousSMul G X]
  [IsPretransitive G X]`), with underlying equivalence
  `TauCeti.quotientStabilizerEquiv G b`; `@[simp]` lemmas `_toEquiv`, `_mk`
  (the coset of `g` goes to `g • b`) and `_smul` (equivariance), as for Tau
  Ceti's compact version. The namespace is Mathlib's `MulAction`, where the
  stabilizer lives; `TauCeti` belongs to another project.

### `Topology/ComplexStructure/Orbit.lean`

- `quotientRealifyHomeomorph ι :
  GL (ι ⊕ ι) ℝ ⧸ (Matrix.GeneralLinearGroup.realify ι ℂ).range ≃ₜ
  AlmostComplexStructure (StdSpace ι)`, the composite of
  `MulAction.quotientStabilizerHomeomorphOfSigmaCompact` with the equality of
  subgroups `stabilizer_stdComplexStructure`;
  `@[simp] quotientRealifyHomeomorph_mk : quotientRealifyHomeomorph ι g = g • J₀`.
- `isClopen_setOf_isPositivelyOriented : IsClopen {J | IsPositivelyOriented J}`:
  it and its complement are the images of the open sets `{det > 0}` and
  `{det < 0}` of `GL (ι ⊕ ι) ℝ` under the open orbit map.

### `Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Polar.lean`

- `Units.polarUnitary_mul_rpow_mul_star_of_mul_self_eq_neg_one (a : Aˣ)
  (ha : (a : A) * a = -1) (s : ℝ) :
  (a.polarUnitary : A) * CFC.sqrt ((a : A) * star (a : A)) ^ s *
      star (a.polarUnitary : A) =
    CFC.sqrt ((a : A) * star (a : A)) ^ (-s)`, with the coercions to `A` of
  Tau Ceti's `coe_polarUnitary` and `sqrt_mul_star_mul_polarUnitary`, so
  that it rewrites together with them. The typeclass context is the one under
  which Tau Ceti's file states `Units.polarUnitary` and
  `CFC.rpow_unitary_mul_mul_star` (an ordered star ring with a continuous
  functional calculus over `ℝ` for self-adjoint elements,
  `[NonnegSpectrumClass ℝ A] [IsSemitopologicalRing A] [T2Space A]`; every
  C⋆-algebra qualifies). The proof is the computation of decision 5.

### `Analysis/Matrix/Polar/Deformation.lean`

- `Matrix.GeneralLinearGroup.polarDeformation_mul_self_of_mul_self_eq_neg_one
  {A : GL n 𝕜} (hA : (A : Matrix n n 𝕜) * A = -1) (t : ℝ) :
  (polarDeformation A t : Matrix n n 𝕜) * polarDeformation A t = -1`, for
  `RCLike 𝕜`, from the previous lemma with the matrix C⋆-algebra structure
  that Tau Ceti's `polarDeformation` uses.

### `Topology/ComplexStructure/Orthogonal.lean`

- `orthogonalComplexStructures ι : Set (AlmostComplexStructure (StdSpace ι)) :=
  {J | ∀ v, ‖J v‖ = ‖v‖}`, the structures compatible with the Euclidean
  metric, in the form of Tau Ceti's hypotheses; `mem_orthogonalComplexStructures`
  (`J ∈ orthogonalComplexStructures ι ↔ ∀ v, ‖J v‖ = ‖v‖`, by `(rfl)`),
  `mem_orthogonalComplexStructures_iff_inner` (`⟪J v, J w⟫ = ⟪v, w⟫`),
  `mem_orthogonalComplexStructures_iff_mem_orthogonalGroup`
  (through `AlmostComplexStructure.homeomorphMatrix`),
  `@[simp] stdComplexStructure_mem_orthogonalComplexStructures`, and
  `isCompact_orthogonalComplexStructures`.
- `complexStructurePolarRetraction ι :
  C(AlmostComplexStructure (StdSpace ι), orthogonalComplexStructures ι)`,
  the structure of the orthogonal polar factor of the matrix of `J`; with
  `complexStructurePolarRetraction_apply` (under `homeomorphMatrix`, the
  matrix of the retraction of `J` is the matrix of `Units.polarUnitary` of the
  matrix of `J`), and `complexStructurePolarRetraction_of_mem` (it fixes
  orthogonal structures).
- `complexStructurePolarHomotopy ι :
  (ContinuousMap.id _).HomotopyRel
    ((ContinuousMap.subtypeVal).comp (complexStructurePolarRetraction ι))
    (orthogonalComplexStructures ι)`,
  at time `t` the structure of `polarDeformation` of the matrix of `J` at
  time `t`; `complexStructurePolarHomotopy_apply`.
- `orthogonalComplexStructuresHomotopyEquiv ι :
  orthogonalComplexStructures ι ≃ₕ AlmostComplexStructure (StdSpace ι)`, from
  `ofDeformationRetraction`.

### `Topology/ComplexStructure/Oriented.lean`

- The action of `specialOrthogonalGroup (ι ⊕ ι) ℝ` from `Action.lean` (with
  `n = ι ⊕ ι`) preserves the orthogonal and the positively oriented
  structures.
- `map_stabilizer_specialOrthogonalGroup_stdComplexStructure`, an equality of
  submonoids of `Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ`:
  ```lean
  (MulAction.stabilizer (specialOrthogonalGroup (ι ⊕ ι) ℝ) J₀).toSubmonoid.map
      (specialOrthogonalGroup (ι ⊕ ι) ℝ).subtype =
    (Matrix.unitaryGroup ι ℂ).map (Matrix.realifyAlgHom ι ℂ)
  ```
  from `Matrix.orthogonalGroup_inf_centralizer_J` and `Matrix.det_realify`.
- `exists_specialOrthogonalGroup_smul_stdComplexStructure_eq
  (hJ : J ∈ orthogonalComplexStructures ι) (hJ' : IsPositivelyOriented J) :
  ∃ g : specialOrthogonalGroup (ι ⊕ ι) ℝ, g • J₀ = J`,
  from `exists_adapted_orthonormalBasis` and
  `isPositivelyOriented_transport_iff`.
- `quotientUnitaryHomeomorph ι :
  specialOrthogonalGroup (ι ⊕ ι) ℝ ⧸ MulAction.stabilizer _ J₀ ≃ₜ
  {J // J ∈ orthogonalComplexStructures ι ∧ IsPositivelyOriented J}`, Tau
  Ceti's `quotientStabilizerHomeomorph` for the action of
  `specialOrthogonalGroup` on that subtype (transitive by the previous
  lemma; the quotient of a compact group is compact, the subtype is
  Hausdorff); `@[simp] quotientUnitaryHomeomorph_mk`.
- `isPathConnected_setOf_isPositivelyOriented` (each structure is joined by
  the polar homotopy, inside the clopen set, to an orthogonal positively
  oriented one, and these form the image of the path-connected group
  $\mathrm{SO}(2n)$); `connectedComponent_stdComplexStructure :
  connectedComponent J₀ = {J | IsPositivelyOriented J}`.
- `nat_card_connectedComponents_almostComplexStructure_stdSpace [Nonempty ι] :
  Nat.card (ConnectedComponents (AlmostComplexStructure (StdSpace ι))) = 2`,
  and for the erratum
  `nat_card_connectedComponents_almostComplexStructure_stdSpace_of_isEmpty
  [IsEmpty ι] : … = 1`.
- `positivelyOrientedHomotopyEquiv ι :
  {J : AlmostComplexStructure (StdSpace ι) // IsPositivelyOriented J} ≃ₕ
  specialOrthogonalGroup (ι ⊕ ι) ℝ ⧸ MulAction.stabilizer _ J₀`: Tau Ceti's
  `ContinuousMap.HomotopyEquiv.ofWeakDeformationRetraction` for the polar
  homotopy, with `A` the orthogonal positively oriented structures and `B`
  the positively oriented ones (the homotopy stays in `B` since the set is
  clopen), reversed and composed with `quotientUnitaryHomeomorph`.
- Dimension four: `stdSpaceQuaternionIsometry : StdSpace (Fin 2) ≃ₗᵢ[ℝ] ℍ[ℝ]`,
  defined as `(LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).trans
  Quaternion.linearIsometryEquivTuple.symm`, where `e : Fin 2 ⊕ Fin 2 ≃ Fin 4`
  sends `inl 0, inr 0, inl 1, inr 1` to `0, 1, 2, 3` (not `finSumFinEquiv`,
  whose order differs), so that $z\mapsto x_1+y_1i+x_2j+y_2k$; with `@[simp]`
  lemmas `stdSpaceQuaternionIsometry_apply` (its four components) and
  `stdSpaceQuaternionIsometry_symm_apply` (the coordinates of the vector of a
  quaternion);
  `quaternionComplexStructure (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
  AlmostComplexStructure (StdSpace (Fin 2))` (left multiplication by
  $u_0i+u_1j+u_2k$, read through the isometry; its square is $-|u|^2=-1$),
  with `quaternionComplexStructure_apply` (that formula, as a `@[simp]`
  lemma), orthogonal and positively oriented (it is $J_0$ at $u=(1,0,0)$, and
  the sphere is connected), and `quaternionComplexStructure_apply_single`: its
  value on the basis vector $x_1$ is the vector $u_0y_1+u_1x_2+u_2y_2$;
  `sphereHomeomorphOrthogonal :
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
  {J // J ∈ orthogonalComplexStructures (Fin 2) ∧ IsPositivelyOriented J}`
  (injectivity from the value on $x_1$; surjectivity because an orthogonal
  positively oriented structure is determined by its value on one unit vector:
  on the orthogonal complement of the plane that vector spans with its image
  it is one of the two rotations by a right angle, and the orientation picks
  one, using `exists_unitary_orthonormalBasis_of_norm_eq_one`), with
  `@[simp] sphereHomeomorphOrthogonal_apply` (`u` goes to
  `quaternionComplexStructure u`) and `sphereHomeomorphOrthogonal_symm_apply`
  (the imaginary part of the quaternion of $J(x_1)$);
  `positivelyOrientedHomotopyEquivSphere :
  {J : AlmostComplexStructure (StdSpace (Fin 2)) // IsPositivelyOriented J} ≃ₕ
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`.

## Main results

- `exists_transport_stdComplexStructure_eq` (in
  `LinearAlgebra/ComplexStructure/Standard.lean`):
  ```lean
  theorem exists_transport_stdComplexStructure_eq [FiniteDimensional ℝ V]
      (J : AlmostComplexStructure V) (h : finrank ℝ V = 2 * Fintype.card ι) :
      ∃ Φ : StdSpace ι ≃ₗ[ℝ] V, (stdComplexStructure ι).transport Φ = J
  ```
  with `transport_eq_transport_iff` (in `Action.lean`, for `J = J₀`): two such `Φ`, `Ψ`
  give the same structure if and only if `Φ ≪≫ₗ Ψ.symm`, the map
  $\Psi^{-1}\circ\Phi$ of `StdSpace ι` to itself, is complex linear for `J₀`
  (`TauCeti.IsComplexLinearMap`); since `transport e` is conjugation by `e`,
  this is the condition that $\Psi^{-1}\Phi$ commutes with $J_0$.
- `instance : MulAction.IsPretransitive (GL (ι ⊕ ι) ℝ) (AlmostComplexStructure (StdSpace ι))`
  (from the previous theorem with `V = StdSpace ι` and `ofEuclideanCLE`), and
  ```lean
  theorem stabilizer_stdComplexStructure :
      MulAction.stabilizer (GL (ι ⊕ ι) ℝ) (stdComplexStructure ι) =
        (Matrix.GeneralLinearGroup.realify ι ℂ).range
  ```
  from the matrix dictionary of *Standard model* (a matrix commutes with
  `Matrix.J` if and only if its map commutes with `J₀`) and
  `mem_range_realify_iff`.
- `isPositivelyOriented_iff_orientation`:
  ```lean
  theorem isPositivelyOriented_iff_orientation {k : ℕ}
      (hk : finrank ℝ (StdSpace ι) = k) (J : AlmostComplexStructure (StdSpace ι)) :
      IsPositivelyOriented J ↔
        ∀ {m : ℕ} (b : Module.Basis (Fin m × Fin 2) ℝ (StdSpace ι))
          (_ : ∀ i, b (i, 1) = J (b (i, 0))) (h : m * 2 = k),
          (b.reindex (finProdFinEquiv.trans (finCongr h))).orientation =
            (stdForm ι).orientation hk
  ```
  from `Tames.orientation_reindex` for `J₀` (tamed by $\omega_0$ by
  `stdForm_compatible`) and `isPositivelyOriented_transport_iff`; adapted
  bases exist by `exists_basis_apply_one_eq`, so the right side is not
  vacuous.
- The topological results listed above: `quotientRealifyHomeomorph`,
  `connectedComponent_stdComplexStructure`,
  `nat_card_connectedComponents_almostComplexStructure_stdSpace`,
  `positivelyOrientedHomotopyEquiv`, `positivelyOrientedHomotopyEquivSphere`.
- The milestone, one theorem in `Topology/ComplexStructure/Oriented.lean`,
  for every `n : ℕ`, with the universe `u` of the spaces `V`:
  ```lean
  theorem complexStructures_classification (n : ℕ) :
      (∀ (V : Type u) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
          (J : AlmostComplexStructure V), finrank ℝ V = 2 * n →
          ∃ Φ : StdSpace (Fin n) ≃ₗ[ℝ] V, (stdComplexStructure (Fin n)).transport Φ = J) ∧
      Nonempty (GL (Fin n ⊕ Fin n) ℝ ⧸ (Matrix.GeneralLinearGroup.realify (Fin n) ℂ).range ≃ₜ
          AlmostComplexStructure (StdSpace (Fin n))) ∧
      (n ≠ 0 → Nat.card (ConnectedComponents (AlmostComplexStructure (StdSpace (Fin n)))) = 2) ∧
      (∀ (hk : finrank ℝ (StdSpace (Fin n)) = n * 2) J,
          J ∈ connectedComponent (stdComplexStructure (Fin n)) ↔
          ∀ (b : Module.Basis (Fin n × Fin 2) ℝ (StdSpace (Fin n)))
            (_ : ∀ i, b (i, 1) = J (b (i, 0))),
            (b.reindex finProdFinEquiv).orientation = (stdForm (Fin n)).orientation hk) ∧
      (MulAction.stabilizer (specialOrthogonalGroup (Fin n ⊕ Fin n) ℝ)
          (stdComplexStructure (Fin n))).toSubmonoid.map
          (specialOrthogonalGroup (Fin n ⊕ Fin n) ℝ).subtype =
        (Matrix.unitaryGroup (Fin n) ℂ).map (Matrix.realifyAlgHom (Fin n) ℂ) ∧
      Nonempty (connectedComponent (stdComplexStructure (Fin n)) ≃ₕ
          specialOrthogonalGroup (Fin n ⊕ Fin n) ℝ ⧸
            MulAction.stabilizer (specialOrthogonalGroup (Fin n ⊕ Fin n) ℝ)
              (stdComplexStructure (Fin n))) ∧
      Nonempty (connectedComponent (stdComplexStructure (Fin 2)) ≃ₕ
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  ```
  The fourth conjunct binds the dimension proof `hk` that the symplectic
  orientation needs; such a proof exists (`finrank_euclideanSpace`), and the
  orientation does not depend on it. It says that the component of $J_0$
  consists of the structures whose adapted bases induce the standard
  orientation. The fifth identifies the stabilizer of $J_0$ in
  $\mathrm{SO}(2n)$ with the realified unitary group $\mathrm{U}(n)$, so that
  the sixth is the homotopy type $\mathrm{SO}(2n)/\mathrm{U}(n)$. The sixth and
  seventh are about the component of $J_0$ itself, obtained from
  `positivelyOrientedHomotopyEquiv` and
  `positivelyOrientedHomotopyEquivSphere` by rewriting with
  `connectedComponent_stdComplexStructure`. The third conjunct has the
  hypothesis `n ≠ 0` of decision 8. Its docstring ends with
  "Milestone: *Linear complex structures are standard*."

## What it uses

- *Standard model*: `StdSpace`, `stdComplexStructure` with
  `stdComplexStructure_def` (the transport of `ofComplexModule (ι → ℂ)` along
  `complexToRealEuclidean ι`) and `stdComplexStructure_eq_toEuclideanLin_J`,
  `stdForm`, `stdForm_compatible`, and the matrix dictionary (commuting with
  `Matrix.J`).
- Tau Ceti and Mathlib, as listed in the first section.
- No other part. *Compatible complex structures* builds on this part: it uses
  the action of `V ≃ₗ[ℝ] V` (`Action.lean`),
  `exists_transport_stdComplexStructure_eq`, and the topological facts of
  `Topology/ComplexStructure/Basic.lean`.

## Building issues

Each is a few hundred lines; each is blocked by the ones before it that it
names, and the first two by the *Standard model* issues (#7, #8).

1. **Complex structures: the standard form and the action of matrices.** The
   actions of `V ≃ₗ[ℝ] V`, of `GL n ℝ` and of `specialOrthogonalGroup n ℝ` in
   `LinearAlgebra/ComplexStructure/Action.lean`;
   `exists_transport_stdComplexStructure_eq`,
   `transport_eq_transport_iff`, transitivity and
   `stabilizer_stdComplexStructure`, in
   `LinearAlgebra/ComplexStructure/Standard.lean`. About 200 lines. Blocked
   by #7 and #8.
2. **Complex structures: positively oriented structures.**
   `IsPositivelyOriented` with its API and
   `isPositivelyOriented_iff_orientation`, in
   `LinearAlgebra/ComplexStructure/Standard.lean`. About 250 lines. Blocked
   by 1.
3. **Complex structures: the homogeneous space GL(2n,ℝ)/GL(n,ℂ).**
   `MulAction.quotientStabilizerHomeomorphOfSigmaCompact` in
   `Topology/Algebra/GroupAction/Transitive.lean`; the closed embedding,
   `T2Space` and `LocallyCompactSpace`, `homeomorphMatrix` and the continuity
   of the actions in `Topology/ComplexStructure/Basic.lean`;
   `quotientRealifyHomeomorph` and
   `isClopen_setOf_isPositivelyOriented` in
   `Topology/ComplexStructure/Orbit.lean`. About 300 lines. Blocked by 2.
4. **Complex structures: retraction onto the orthogonal structures.** The
   conjugation lemma of
   `Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Polar.lean`, the
   lemma of `Analysis/Matrix/Polar/Deformation.lean`, and
   `Topology/ComplexStructure/Orthogonal.lean`. About 300 lines. Blocked by 3.
5. **Complex structures: components and the homotopy type SO(2n)/U(n).** The
   stabilizer of $J_0$ in `specialOrthogonalGroup`, transitivity on the
   orthogonal positively oriented structures, `quotientUnitaryHomeomorph`,
   the component of $J_0$, the count of components (with the case of empty
   `ι`), and `positivelyOrientedHomotopyEquiv`, in
   `Topology/ComplexStructure/Oriented.lean`. About 350 lines. Blocked by 4.
6. **Complex structures: the case of ℝ⁴ and the milestone.** The quaternion
   structures, `sphereHomeomorphOrthogonal`,
   `positivelyOrientedHomotopyEquivSphere` and
   `complexStructures_classification`, in the same file. About 300 lines.
   Blocked by 5.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third
  edition][McDuffSalamon2017], Section 2.5, Propositions 2.5.1 and 2.5.2.
