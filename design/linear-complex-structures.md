# Linear complex structures

The detailed design of part 8 of `DESIGN.md`, *Linear complex structures*. It
proves the milestone *Linear complex structures are standard* of
`atlas/linear-symplectic-geometry.md`, following McDuff–Salamon
[McDuffSalamon2017], Propositions 2.5.1 and 2.5.2.

All declarations of Tau Ceti and Mathlib named below were checked against
Tau Ceti `v4.37.0-rc1` and its Mathlib, the versions pinned when this file
was written; `lakefile.toml` pins Tau Ceti `c9d170eed5a8` now. Paths of Tau
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
   finite index type `ι`. It replaces the route through Tau Ceti's
   `ContinuousLinearMap.exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul`
   (`Geometry/Symplectic/Complex/Module/Conjugacy.lean`), whose dimension is
   only existential.
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

Files are under `SymplecticGeometry/`. Each of the part's files has
the topic its path says. Besides the standard model, the orbit space and the
oriented components, they hold the actions on complex structures, their
general topology, general lemmas on complex linear maps, the general orbit–stabilizer homeomorphism, the units of
square $-1$, the inverse of
an element and of a matrix of square $-1$, the agreement of the
matrices given by `Matrix.toEuclideanCLM` and `Matrix.toEuclideanLin`, a star-ring
lemma on elements of square $-1$, the conjugation identity for units of square $-1$, the polar deformation of
matrices of square $-1$, the orthogonal complex structures, the map from
$\mathbb{R}^3$ to the pure quaternions, and the
orientation of bases adapted to a transported structure. The actions
and their topology are stated for any space, so that later work can use
them. The library's `Geometry/Symplectic/Orientation.lean` has the same
path as the Tau Ceti file cited in the first section, on purpose: its one
lemma extends that file and is a candidate to move there.

| File | Contents |
|---|---|
| `LinearAlgebra/ComplexStructure/Action.lean` | the action of `V ≃ₗ[ℝ] V`, and of `GL n ℝ` and `specialOrthogonalGroup n ℝ` on the structures of `EuclideanSpace ℝ n` |
| `LinearAlgebra/ComplexStructure/Hom.lean` | the inverse of a complex linear isomorphism, complex linear left and right inverses, the inclusion of an invariant subspace, and the complex linear endomorphisms as those commuting with the structure |
| `Topology/ComplexStructure/Basic.lean` | the closed embedding into operators, `T2Space` and `LocallyCompactSpace`, for finite-dimensional normed `V`; the matrix homeomorphism and continuity of the actions, for `EuclideanSpace ℝ n` |
| `Geometry/Symplectic/Orientation.lean` | bases adapted to the transport of a tamed structure induce the transported symplectic orientation |
| `LinearAlgebra/ComplexStructure/Standard.lean` | the isomorphism $\Phi$, transitivity, the stabilizer, positively oriented structures, compatibility with $\omega_0$ under symplectic matrices and the action of `Matrix.symplecticGroup ι ℝ` on the compatible structures |
| `Topology/Algebra/GroupAction/Transitive.lean` | the orbit–stabilizer homeomorphism for σ-compact groups |
| `Topology/ComplexStructure/Orbit.lean` | the space as GL(2n,ℝ)/GL(n,ℂ), the positively oriented structures form a clopen set |
| `Algebra/Ring/Units.lean` | an element of square $-1$ is a unit |
| `Algebra/GroupWithZero/Units/Basic.lean` | an element of square $-1$ has `Ring.inverse` its negative |
| `LinearAlgebra/Matrix/NonsingularInverse.lean` | a matrix of square $-1$ has inverse its negative |
| `Analysis/CStarAlgebra/Matrix.lean` | the matrix of a linear endomorphism of `EuclideanSpace 𝕜 n` is the same through `Matrix.toEuclideanCLM` and `Matrix.toEuclideanLin` |
| `Algebra/Star/Basic.lean` | in a star ring, an element of square $-1$ has $a^\ast a = (a a^\ast)^{-1}$ |
| `Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Polar.lean` | the polar unitary factor of a unit of square $-1$ inverts the powers of its positive factor |
| `Analysis/Matrix/Polar/Deformation.lean` | the polar deformation preserves square $-1$ |
| `Topology/ComplexStructure/Orthogonal.lean` | the orthogonal complex structures, the deformation retraction onto them |
| `Analysis/Quaternion.lean` | the linear isometry from `EuclideanSpace ℝ (Fin 3)` to the pure quaternions, and the square of its values |
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
  for any `[AddCommGroup V] [Module ℝ V]`; with `@[simp] smul_def` (by
  `(rfl)`), and `smul_apply : (e • J) v = e (J (e.symm v))` and
  `toLinearMap_smul`, not simp. The axioms are `transport_refl` and
  `transport_trans`.
- **Simp normal form.** For a linear automorphism, `simp` writes the action
  as Tau Ceti's `transport`: `smul_def` turns `e • J` into `J.transport e`,
  and Tau Ceti's simp lemmas (`transport_apply`, `transport_toLinearMap`,
  `transport_trans`, …) take over, so `smul_apply` and `toLinearMap_smul`
  would be redundant as simp lemmas. So that the group laws of the action
  survive this rewriting, the group operations of `V ≃ₗ[ℝ] V` inside
  `transport` are rewritten to Tau Ceti's form by `@[simp]` lemmas, all by
  `(rfl)` or `transport_refl`: `transport_one : J.transport 1 = J`,
  `transport_mul : J.transport (e * f) = (J.transport f).transport e` and
  `transport_inv : J.transport e⁻¹ = J.transport e.symm`. The right side of
  `transport_mul` is nested, not `J.transport (f ≪≫ₗ e)`, so that a product
  or an inverse in a factor is still the argument of `transport` when `simp`
  reaches it. Tau Ceti's `transport_trans` then gathers the nested
  transports into one composite bracketed to the left, while Mathlib's
  cancellation lemmas for `e ≪≫ₗ e.symm` need it bracketed to the right.
  Mathlib's `LinearEquiv.trans_assoc` cannot serve, since `simp` cannot
  find its composite ring homomorphisms, so the file adds the same-ring form
  `@[simp] LinearEquiv.trans_assoc_id : (a ≪≫ₗ b) ≪≫ₗ c = a ≪≫ₗ (b ≪≫ₗ c)`
  (by `(rfl)`, over any semiring), in Mathlib's namespace so that it can move
  upstream. It rebrackets every composite to the right, at any depth. With
  these lemmas `simp` proves `e⁻¹ • e • J = J`,
  `e⁻¹ • f⁻¹ • g⁻¹ • g • f • e • J = J`,
  `(e * f * g)⁻¹ • (e * f * g) • J = J`, `f⁻¹ • e⁻¹ • e • f • g • J = g • J`,
  `e • f • g • h • J = (e * f * g * h) • J`,
  `(e * f * g) • J = e • f • g • J` and
  `(e * f)⁻¹ • J = f⁻¹ • e⁻¹ • J`. Lemmas whose right side is an action of
  `V ≃ₗ[ℝ] V` state it with `transport`, as `ofEuclideanCLE_smul :
  ofEuclideanCLE Φ • J = J.transport Φ.toLinearEquiv` (`@[simp]`) does. The
  matrix actions keep `•` as their normal form.
- `instance instMulActionGeneralLinearGroup :
  MulAction (GL n ℝ) (AlmostComplexStructure (EuclideanSpace ℝ n))`, the
  action of matrices,
  `g • J = J.transport ((g : Matrix _ _ ℝ).toEuclideanCLE g.det_ne_zero).toLinearEquiv`;
  built as `MulAction.compHom` of the previous action along
  `Matrix.GeneralLinearGroup.ofEuclideanCLE.symm` followed by forgetting
  continuity. API: `generalLinearGroup_smul_def` (the formula above; not
  `(rfl)`, since Tau Ceti does not expose the body of `ofEuclideanCLE`),
  `generalLinearGroup_smul_apply :
  (g • J) v = Matrix.toEuclideanLin g (J (Matrix.toEuclideanLin (↑g)⁻¹ v))`
  (not simp: `simp` proves it from the next lemma) and
  `@[simp] toLinearMap_generalLinearGroup_smul :
  (g • J).toLinearMap = toEuclideanLin g ∘ₗ J.toLinearMap ∘ₗ toEuclideanLin (↑g)⁻¹`.
- `transport_eq_transport_iff`: for any `J` and
  `Φ Ψ : V ≃ₗ[ℝ] W`, `J.transport Φ = J.transport Ψ` if and only if
  `Φ ≪≫ₗ Ψ.symm` is complex linear for `J`.
- `exists_linearIsometryEquiv_transport_eq`: two norm-preserving complex
  structures on finite-dimensional real inner product spaces of equal
  dimension are conjugate by a linear isometry (it composes the isometries with
  `ℂⁿ` from `exists_linearIsometryEquiv_euclideanSpace`, and concludes with
  `transport_eq_iff_isComplexLinearMap`); the transitivity of `SO(2n)` in
  `Oriented.lean` uses it.
- `instance instMulActionSpecialOrthogonalGroup :
  MulAction (specialOrthogonalGroup n ℝ) (AlmostComplexStructure (EuclideanSpace ℝ n))`,
  `MulAction.compHom` of the matrix action along the inclusion
  `Unitary.toUnits.comp (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup)`
  into `GL n ℝ` (no new name for that homomorphism). It has no apply lemma of
  its own: `@[simp] specialOrthogonalGroup_smul_def` rewrites `g • J` as the
  action of that unit, so `toLinearMap_generalLinearGroup_smul` serves both
  actions.
- `TauCeti.SymplecticForm.IsSymplectomorphism.compatible_transport_iff
  (he : ω₁.IsSymplectomorphism ω₂ e) (J) :
  ω₂.Compatible (J.transport e) ↔ ω₁.Compatible J`, for `e : V ≃ₗ[ℝ] W`,
  from Tau Ceti's `compatible_transport_iff` and
  `isSymplectomorphism_iff_transport_eq`.
- `toEuclideanLin_symm_mul_self (J : AlmostComplexStructure (EuclideanSpace ℝ n)) :
  toEuclideanLin.symm J.toLinearMap * toEuclideanLin.symm J.toLinearMap = -1`,
  the matrix of a complex structure squares to $-1$. It sits here, not in
  *Standard model*'s `Symplectic/Standard/Matrix.lean`, so that
  `Topology/ComplexStructure/Basic.lean` can use it; its users in other
  parts reach it through their imports.

### `LinearAlgebra/ComplexStructure/Hom.lean`

General lemmas on Tau Ceti's `TauCeti.IsComplexLinearMap`, kept apart from
the actions so that a file needing only them does not import `Action.lean`.
The file imports only Tau Ceti; its lemmas belong upstream beside Tau Ceti's
`Geometry/Symplectic/Complex/Module/Hom.lean`.

- `TauCeti.IsComplexLinearMap.symm_linearEquiv
  (h : IsComplexLinearMap J J' e.toLinearMap) :
  IsComplexLinearMap J' J e.symm.toLinearMap`, for `e : V ≃ₗ[ℝ] W`: the
  bundled form of Tau Ceti's `IsComplexLinear.symm`, obtained through the
  bridge `isComplexLinearMap_iff_isComplexLinear`, as Tau Ceti does for
  `IsComplexLinearMap.comp`.
- `TauCeti.IsComplexLinearMap.exists_leftInverse_of_injective
  (hF : IsComplexLinearMap J J' F) (hinj : Function.Injective F) :
  ∃ G : W →ₗ[ℝ] V, IsComplexLinearMap J' J G ∧ G ∘ₗ F = LinearMap.id` and
  `TauCeti.IsComplexLinearMap.exists_rightInverse_of_surjective
  (hF : IsComplexLinearMap J J' F) (hsurj : Function.Surjective F) :
  ∃ G : W →ₗ[ℝ] V, IsComplexLinearMap J' J G ∧ F ∘ₗ G = LinearMap.id`:
  Mathlib's `LinearMap.exists_leftInverse_of_injective` and
  `LinearMap.exists_rightInverse_of_surjective` over `ℂ`, for the complex
  module structures of `J` and `J'`, with scalars restricted to `ℝ`.
- `TauCeti.AlmostComplexStructure.isComplexLinearMap_subtype
  (hW : ∀ v ∈ W, J v ∈ W) : IsComplexLinearMap (J.restrict W hW) J W.subtype`,
  for `W : Submodule ℝ V`, moved here from *Adjunction*'s
  `LinearAlgebra/ComplexStructure/Orientation.lean`.
- `TauCeti.AlmostComplexStructure.isComplexLinearMap_self_iff_commute :
  IsComplexLinearMap J J f ↔ Commute f J.toLinearMap`, for
  `f : Module.End ℝ V`.

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
  The square of the matrix is $-1$ by `toEuclideanLin_symm_mul_self`
  (`Action.lean`), through `Matrix.toEuclideanCLM_symm_toContinuousLinearMap`
  (`Analysis/CStarAlgebra/Matrix.lean`), which also gives
  `coe_homeomorphMatrix`.
- `TauCeti.AlmostComplexStructure.toGeneralLinearGroup J : GL n ℝ`, the matrix
  of `J` as a unit (its inverse is the matrix of `-J`), with
  `coe_toGeneralLinearGroup`, `coe_toGeneralLinearGroup_inv` (not `@[simp]`;
  `simp` reaches the `@[simp]` lemma
  `inv_toEuclideanCLM_symm_toContinuousLinearMap` instead) and
  `continuous_toGeneralLinearGroup`; the polar deformation of
  `Orthogonal.lean` is applied to it.
- `instance : ContinuousSMul (GL n ℝ) (AlmostComplexStructure (EuclideanSpace ℝ n))`
  (the matrix of `g • J` is $gJg^{-1}$), and from it the `ContinuousSMul`
  instance of `specialOrthogonalGroup n ℝ`.

### `Geometry/Symplectic/Orientation.lean`

- `TauCeti.SymplecticForm.Tames.orientation_reindex_transport (hJ : ω.Tames J)
  (e : V ≃ₗ[ℝ] W) (hk : finrank ℝ V = k)
  (hb : ∀ i, b (i, 1) = J.transport e (b (i, 0))) (h : n * 2 = k)`: the
  reindexed basis `b` of `W` has orientation
  `Orientation.map (Fin k) e (ω.orientation hk)`. It is Tau Ceti's
  `Tames.orientation_reindex` for the tamed pair `(ω.transport e,
  J.transport e)` (`Tames.transport`), followed by
  `IsSymplectomorphism.map_orientation`. It lives in Tau Ceti's namespace
  `TauCeti.SymplecticForm` and at Tau Ceti's path, so that it can move
  upstream next to `Tames.orientation_reindex` unchanged.

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

*Symplectic matrices and compatible structures.*

- `compatible_generalLinearGroup_smul_iff (hg : g ∈ GLSymplectic ι ℝ) (J) :
  (stdForm ι).Compatible (g • J) ↔ (stdForm ι).Compatible J`, and the
  instance `instMulActionSymplecticGroupCompatible` of
  `Matrix.symplecticGroup ι ℝ` on `{J // (stdForm ι).Compatible J}`, through
  `GLSymplectic.ofSymplecticGroup`, with `@[simp] coe_symplecticGroup_smul`
  (by `(rfl)`). The first is
  `SymplecticForm.IsSymplectomorphism.compatible_transport_iff` (`Action.lean`)
  applied to *Standard model*'s
  `mem_GLSymplectic_iff_isSymplectomorphism`.
- `exists_symplecticGroup_smul_stdComplexStructure_eq (hJ : (stdForm ι).Compatible J) :
  ∃ Ψ : Matrix.symplecticGroup ι ℝ, GLSymplectic.ofSymplecticGroup ι ℝ Ψ • J₀ = J`,
  and the instance `instIsPretransitiveSymplecticGroupCompatible`: the action
  above is transitive. The first reads the isomorphism of
  `compatible_iff_exists_isSymplectomorphism_stdForm`
  (`LinearAlgebra/Symplectic/Compatible.lean`, *Compatible complex structures*)
  as a matrix with `Matrix.GeneralLinearGroup.ofEuclideanCLE`.

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
- `isClopen_setOfPred_isPositivelyOriented : IsClopen {J | IsPositivelyOriented J}`:
  it and its complement are the images of the open sets `{det > 0}` and
  `{det < 0}` of `GL (ι ⊕ ι) ℝ` under the open orbit map.

### `Algebra/Ring/Units.lean`

- `isUnit_of_mul_self_eq_neg_one (ha : a * a = -1) : IsUnit a`, in
  `SymplecticGeometry`, for `[Monoid M] [HasDistribNeg M]`. It imports only
  `Mathlib.Algebra.Ring.Units`, whose level it has.

### `Algebra/GroupWithZero/Units/Basic.lean`

- `Ring.inverse_eq_neg_of_mul_self_eq_neg_one (ha : a * a = -1) : a⁻¹ʳ = -a`,
  for `[MonoidWithZero M] [HasDistribNeg M]`. It imports
  `Algebra/Ring/Units.lean`.

### `LinearAlgebra/Matrix/NonsingularInverse.lean`

- `Matrix.inv_eq_neg_of_mul_self_eq_neg_one (hA : A * A = -1) : A⁻¹ = -A`,
  over a commutative ring, from the previous lemma by Mathlib's
  `Matrix.nonsing_inv_eq_ringInverse`. `toGeneralLinearGroup` and the star-ring
  lemma below are built on these.

### `Analysis/CStarAlgebra/Matrix.lean`

- `Matrix.toEuclideanCLM_symm_toContinuousLinearMap :
  toEuclideanCLM.symm (LinearMap.toContinuousLinearMap f) = toEuclideanLin.symm f`,
  for any `RCLike 𝕜`; it imports only Mathlib. `Topology/ComplexStructure/Basic.lean`
  uses it.

### `Algebra/Star/Basic.lean`

- `star_mul_self_eq_inverse_of_mul_self_eq_neg_one {a : A} (ha : a * a = -1) :
  star a * a = (a * star a)⁻¹ʳ`, in `SymplecticGeometry`, for any
  `[Ring A] [StarRing A]`. Such an `a` is a unit with inverse `-a`, so this
  follows from Mathlib's `Ring.inverse_mul` and `Ring.inverse_star`. It is
  pure star-ring algebra, so it sits apart from the functional calculus and
  imports only `Mathlib.Algebra.Star.Basic` and
  `Algebra/GroupWithZero/Units/Basic.lean`; the next file uses it.

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

Everything here is stated for `AlmostComplexStructure (EuclideanSpace ℝ n)`,
with `[Fintype n]`, and `[DecidableEq n]` where `homeomorphMatrix` enters;
only the lemma about $J_0$ takes `n = ι ⊕ ι`. Since `StdSpace ι` is an
`abbrev` for `EuclideanSpace ℝ (ι ⊕ ι)`, the results apply to it as they are.

- `orthogonalComplexStructures n :
  Set (AlmostComplexStructure (EuclideanSpace ℝ n)) :=
  {J | ∀ v, ‖J v‖ = ‖v‖}`, the structures compatible with the Euclidean
  metric, in the form of Tau Ceti's hypotheses; `mem_orthogonalComplexStructures`
  (`J ∈ orthogonalComplexStructures n ↔ ∀ v, ‖J v‖ = ‖v‖`, by `(rfl)`),
  `mem_orthogonalComplexStructures_iff_inner` (`⟪J v, J w⟫ = ⟪v, w⟫`),
  `mem_orthogonalComplexStructures_iff_mem_orthogonalGroup`
  (through `AlmostComplexStructure.homeomorphMatrix`),
  `@[simp] stdComplexStructure_mem_orthogonalComplexStructures`
  (`J₀ ∈ orthogonalComplexStructures (ι ⊕ ι)`), and
  `isCompact_orthogonalComplexStructures`.
- `complexStructurePolarRetraction n :
  C(AlmostComplexStructure (EuclideanSpace ℝ n), orthogonalComplexStructures n)`,
  the structure of the orthogonal polar factor of the matrix of `J`; with
  `complexStructurePolarRetraction_apply` (under `homeomorphMatrix`, the
  matrix of the retraction of `J` is the matrix of `Units.polarUnitary` of the
  matrix of `J`), and `complexStructurePolarRetraction_of_mem` (it fixes
  orthogonal structures).
- `complexStructurePolarHomotopy n :
  (ContinuousMap.id _).HomotopyRel
    ((ContinuousMap.subtypeVal).comp (complexStructurePolarRetraction n))
    (orthogonalComplexStructures n)`,
  at time `t` the structure of `polarDeformation` of the matrix of `J` at
  time `t`; `complexStructurePolarHomotopy_apply`.
- `orthogonalComplexStructuresHomotopyEquiv n :
  orthogonalComplexStructures n ≃ₕ AlmostComplexStructure (EuclideanSpace ℝ n)`, from
  `ofDeformationRetraction`.

### `Analysis/Quaternion.lean`

General quaternion material, in Mathlib's namespace `Quaternion`; nothing in
it mentions complex structures.

- `Quaternion.pureOfEuclideanSpace : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] ℍ[ℝ]`,
  $u\mapsto u_0i+u_1j+u_2k$, with `pureOfEuclideanSpace_apply` (that formula,
  by `(rfl)`, not a simp lemma) and the `@[simp]` lemmas
  `re_pureOfEuclideanSpace`, `imI_pureOfEuclideanSpace`,
  `imJ_pureOfEuclideanSpace` and `imK_pureOfEuclideanSpace` for its four
  components; its norm is `LinearIsometry.norm_map`.
- `pureOfEuclideanSpace_mul_self`: the square of the value at `u` is
  $-\|u\|^2$, and `pureOfEuclideanSpace_mul_self_of_norm_eq_one`: at a unit
  vector it is $-1$.

### `Topology/ComplexStructure/Oriented.lean`

- The action of `specialOrthogonalGroup n ℝ` from `Action.lean` preserves and
  reflects orthogonality
  (`specialOrthogonalGroup_smul_mem_orthogonalComplexStructures_iff`, for any
  `n`), and for `n = ι ⊕ ι` positive orientation
  (`isPositivelyOriented_specialOrthogonalGroup_smul_iff`). So the orthogonal
  positively oriented structures form
  `positiveOrthogonalComplexStructures ι :
  SubMulAction (specialOrthogonalGroup (ι ⊕ ι) ℝ) (AlmostComplexStructure (StdSpace ι))`,
  with `@[simp] mem_positiveOrthogonalComplexStructures`; Mathlib's
  `SubMulAction` API gives the action on it, `SubMulAction.val_smul` and
  `SubMulAction.stabilizer_of_subMul`, which `quotientUnitaryHomeomorph` is
  built on.
- `mem_stabilizer_specialOrthogonalGroup_stdComplexStructure_iff`: `g` fixes
  $J_0$ exactly when it commutes with the matrix `J ι ℝ`.
- `map_stabilizer_specialOrthogonalGroup_stdComplexStructure`, an equality of
  submonoids of `Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ`:
  ```lean
  (MulAction.stabilizer (specialOrthogonalGroup (ι ⊕ ι) ℝ) J₀).toSubmonoid.map
      (specialOrthogonalGroup (ι ⊕ ι) ℝ).subtype =
    (Matrix.unitaryGroup ι ℂ).map (Matrix.realifyAlgHom ι ℂ)
  ```
  from `Matrix.orthogonalGroup_inf_centralizer_J` and `Matrix.det_realify`.
- `exists_specialOrthogonalGroup_smul_stdComplexStructure_eq
  (hJ : J ∈ orthogonalComplexStructures (ι ⊕ ι)) (hJ' : IsPositivelyOriented J) :
  ∃ g : specialOrthogonalGroup (ι ⊕ ι) ℝ, g • J₀ = J`,
  from `exists_adapted_orthonormalBasis` and
  `isPositivelyOriented_transport_iff`.
- `quotientUnitaryHomeomorph ι :
  specialOrthogonalGroup (ι ⊕ ι) ℝ ⧸ MulAction.stabilizer _ J₀ ≃ₜ
  positiveOrthogonalComplexStructures ι`, Tau
  Ceti's `quotientStabilizerHomeomorph` for the action of
  `specialOrthogonalGroup` on it (transitive by the previous
  lemma; the quotient of a compact group is compact, the subtype is
  Hausdorff); `@[simp] coe_quotientUnitaryHomeomorph_mk` (the image of the coset
  of `g`, as a structure, is `g • J₀`).
- `isPathConnected_setOfPred_isPositivelyOriented` (each structure is joined by
  the polar homotopy, inside the clopen set, to an orthogonal positively
  oriented one, and these form the image of the path-connected group
  $\mathrm{SO}(2n)$); `connectedComponent_stdComplexStructure :
  connectedComponent J₀ = {J | IsPositivelyOriented J}`, and its path-component
  form `pathComponent_stdComplexStructure`, both from the public
  `IsPositivelyOriented.joined_stdComplexStructure`.
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
  `@[simp] coe_positivelyOrientedHomotopyEquiv_symm_mk` (the coset of `g`
  goes to `g • J₀`) and
  `@[simp] coe_quotientUnitaryHomeomorph_positivelyOrientedHomotopyEquiv`
  (followed by `quotientUnitaryHomeomorph`, a structure goes to its polar
  retraction).
- Dimension four: `stdSpaceQuaternionIsometry : StdSpace (Fin 2) ≃ₗᵢ[ℝ] ℍ[ℝ]`,
  defined as `(LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).trans
  Quaternion.linearIsometryEquivTuple.symm`, where
  `e = TauCeti.finSumFinInterleaveEquiv 2 : Fin 2 ⊕ Fin 2 ≃ Fin (2 * 2)`
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
  positiveOrthogonalComplexStructures (Fin 2)`
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
  from `Tames.orientation_reindex_transport` for `J₀` (tamed by $\omega_0$ by
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
- Tau Ceti and Mathlib, as listed in the first section; besides them,
  `Geometry/Symplectic/Orientation.lean` uses Tau Ceti's
  `SymplecticForm.Tames.transport`, `isSymplectomorphism_iff_transport_eq`
  and `IsSymplectomorphism.map_orientation`.
- Within the part, `isPositivelyOriented_iff_orientation` in `Standard.lean`
  uses `TauCeti.SymplecticForm.Tames.orientation_reindex_transport` from
  `Geometry/Symplectic/Orientation.lean`.
- From *Compatible complex structures*, only the merged file
  `LinearAlgebra/Symplectic/Compatible.lean`, which `Standard.lean` imports for
  `compatible_iff_exists_isSymplectomorphism_stdForm` (transitivity of the
  symplectic group on the compatible structures).
- No other part.

Other parts use merged files of this one. *Compatible complex structures*
imports `Action.lean` into `LinearAlgebra/Symplectic/Compatible.lean`, for
`AlmostComplexStructure.transport_eq_iff_isComplexLinearMap`, `Hom.lean` into
the same file, for `IsComplexLinearMap.symm_linearEquiv`, and
`Topology/ComplexStructure/Basic.lean` into
`Topology/ComplexStructure/Compatible/Matrix.lean`, for
`AlmostComplexStructure.homeomorphMatrix`, `Standard.lean` into
`Topology/Algebra/Matrix/SymplecticGroup/CompactSubgroup.lean`, for
`stabilizer_stdComplexStructure`, and `Topology/ComplexStructure/Orthogonal.lean`
into `Topology/ComplexStructure/Compatible/SymplecticForms.lean`, for
`metricComplexStructures_innerSL`; it states its own equivariance
with Tau Ceti's `transport` directly. *Siegel upper half
space* imports `Action.lean` and `Standard.lean`. `DESIGN.md` records these
two in its build-order table. *Complex submanifolds* imports `Hom.lean` into
`Geometry/Symplectic/Manifold/AlmostComplex/Submanifold.lean`, for
`IsComplexLinearMap.exists_leftInverse_of_injective`, and *Adjunction*
imports it into `LinearAlgebra/ComplexStructure/Orientation.lean`, for
`IsComplexLinearMap.exists_rightInverse_of_surjective`. Since `Standard.lean` in turn imports
`LinearAlgebra/Symplectic/Compatible.lean` of *Compatible complex
structures*, as listed above, each of this part and *Compatible complex
structures* uses a merged file of the other.

## Building issues

Each is a few hundred lines; each is blocked by the ones before it that it
names, and the first two by the *Standard model* issues (#7, #8).

1. **Complex structures: the standard form and the action of matrices.** The
   actions of `V ≃ₗ[ℝ] V`, of `GL n ℝ` and of `specialOrthogonalGroup n ℝ` in
   `LinearAlgebra/ComplexStructure/Action.lean`, with
   `transport_eq_transport_iff`, and `isComplexLinearMap_self_iff_commute`
   (in `LinearAlgebra/ComplexStructure/Hom.lean`);
   `exists_transport_stdComplexStructure_eq`, transitivity and
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
   `isClopen_setOfPred_isPositivelyOriented` in
   `Topology/ComplexStructure/Orbit.lean`. About 300 lines. Blocked by 2.
4. **Complex structures: retraction onto the orthogonal structures.** The
   star-ring lemma of `Algebra/Star/Basic.lean`, the conjugation lemma of
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
   `complexStructures_classification`, in the same file, with the map from
   $\mathbb{R}^3$ to the pure quaternions in `Analysis/Quaternion.lean`.
   About 300 lines.
   Blocked by 5.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third
  edition][McDuffSalamon2017], Section 2.5, Propositions 2.5.1 and 2.5.2.
