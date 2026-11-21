# Contact geometry

This is the detailed design of part 20 of `DESIGN.md`, *Contact geometry*.
It covers the milestones *Contact vector fields and contact Hamiltonians*,
*Contact Darboux theorem*, *Gray stability* and *Legendrian neighbourhood
theorem* of `atlas/symplectic-manifolds.md`, which follow McDuff–Salamon
[McDuffSalamon2017], §3.5: the Reeb field (3.5.2) and the standard form
(3.5.3) on p. 126, Example 3.5.6, Lemma 3.5.14, the discussion of contact
flows on p. 132, and Exercises 3.5.19(i), 3.5.20, 3.5.21 and 3.5.22(i).
Tau Ceti's contact files cite Geiges, *An Introduction to Contact Topology*,
§§1.1, 2.1–2.3 and 2.5, which the new files cite too where they adapt Tau
Ceti's proofs.

All names below are in the namespace given with them; a name written without
one is in `SymplecticGeometry`. Paths of new files are under
`SymplecticGeometry/`; Tau Ceti paths are relative to
`.lake/packages/TauCeti/TauCeti/`, as in `DESIGN.md`. Throughout,
`I : ModelWithCorners ℝ E H` with `[FiniteDimensional ℝ E]`, `M` is a smooth
manifold modelled on `I`, and `α : TauCeti.SmoothForm I M ℝ 1`. The slice of
a form `β` on a product `T × M` (with `T = ℝ` or `T = unitInterval`) at time
`t` is `TauCeti.SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk
contMDiff_id) β`, written $\beta_t$ below; Tau Ceti's Gray and Moser files
write slices this way, and the design adds no name for it.

## What exists, and what the part adds

Tau Ceti already has most of the pointwise theory, all in
`Geometry/Contact/`:

- contact forms and their kernels: `TauCeti.SmoothForm.IsContactForm`,
  `TauCeti.IsContactFormAt`, `TauCeti.SmoothForm.kerDistribution`, the Reeb
  field `TauCeti.SmoothForm.reebVectorField` with `apply_reebVectorField`,
  `mextDeriv_reebVectorField_left`, `eq_reebVectorField_iff` (`Basic.lean`,
  `Reeb.lean`), and rescaling by nowhere vanishing functions
  (`TauCeti.SmoothForm.isContactForm_iff_of_eq_smul`, `Transition.lean`,
  `Rescale.lean`);
- contact structures without a chosen form:
  `TauCeti.IsContactDistribution I n D` for
  `D : Π x : M, Submodule ℝ (TangentSpace I x)`, with
  `TauCeti.isContactDistribution_iff_forall_exists_isContactFormAt` and
  `TauCeti.SmoothForm.isContactForm_iff_isContactDistribution_kerDistribution`
  (`Distribution.lean`), and smoothness of kernels,
  `TauCeti.SmoothForm.isContMDiffDistribution_kerDistribution` (`Levi.lean`);
- contact Hamiltonians: `TauCeti.SmoothForm.IsContactHamiltonianVectorField`
  (the equations $\alpha(X)=H$, $\iota_Xd\alpha=R(H)\alpha-dH$, the page's
  signs), `contactHamiltonianVectorField` with
  `IsContactForm.isContactHamiltonianVectorField_iff_eq`,
  `IsContactHamiltonianVectorField.mlieDerivForm_eq`
  ($\mathcal L_{X_H}\alpha=R(H)\alpha$),
  `IsContactForm.isContactHamiltonianVectorField_iff_mlieDerivForm`,
  `IsContactForm.eq_mvfderiv_reebVectorField_of_mlieDerivForm_apply_eq_smul`,
  `IsContactForm.contactHamiltonianVectorField_one`,
  `IsContactForm.contMDiff_contactHamiltonianVectorField`,
  `IsContactHamiltonianVectorField.mem_kerDistribution_iff`
  (`Hamiltonian.lean`), and `IsContactForm.contactHamiltonianVectorField_of_eq_smul`
  (`Rescale.lean`); the autonomous flow rescaling
  `TauCeti.SmoothForm.IsContactHamiltonianVectorField.mpullback_flowOf_apply`
  (`Flow.lean`);
- contactomorphisms `Diffeomorph.IsContactomorphism`,
  `Diffeomorph.PreservesCoorientation`, `Diffeomorph.IsStrictContactomorphism`
  (`Contactomorphism.lean`);
- Darboux charts: `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart_of_finrank_eq`
  (a chart pulling $dz-\sum_ip_i\,dq_i$, `TauCeti.innerProductContactForm`,
  back to $\alpha$ itself), and for structures
  `TauCeti.IsContactDistribution.exists_darbouxChart`
  (`Darboux/Strict.lean`, `Darboux/Manifold.lean`);
- Gray's theorem for coorientable families over `ℝ`: the horizontal
  contact-Moser field `TauCeti.SmoothForm.contactMoserVectorField` with
  `IsContactForm.eq_contactMoserVectorField_iff` and the change-of-form law
  `IsContactForm.contactMoserVectorField_of_eq_smul`, which allows multipliers
  of either sign (`Moser.lean`); its smooth dependence on a parameter
  (`Family.lean`); and `TauCeti.SmoothForm.grayVectorField`,
  `eq_grayVectorField_iff`, `mlieDerivForm_grayVectorField_add`,
  `grayDiffeomorph`, `mpullback_grayDiffeomorph_apply` (`Gray.lean`), all for
  a form on `ℝ × M` all of whose slices are contact;
- the local Reeb flow out of a slice,
  `TauCeti.mpullback_flowOf_comp_apply_eq_contactization`,
  `TauCeti.SmoothForm.IsContactForm.nondegenerate_bilinFormAt_mextDerivₗ_mpullback`
  and `TauCeti.SmoothForm.IsContactForm.isLocalDiffeomorphAt_flowOf_reebVectorField_comp`
  (`Slice.lean`); the one-jet space
  `TauCeti.CotangentBundle.isContactForm_contactization_liouvilleForm`
  (`Contactization.lean`, with `TauCeti.SmoothForm.contactization θ`
  $=dz-\theta$); Legendrian embeddings `TauCeti.IsLegendrianEmbedding`
  (`Isotropic.lean`).

Mathlib has none of these notions. What is missing, and what this part adds:

1. a type of contact vector fields and the one equivalence between them and
   smooth functions; the characterization of contact fields by their local
   flows; the rescaling formula for time-dependent contact Hamiltonians; and
   $X_H$ as the Reeb field of $\alpha/H$;
2. the normal form in the page's signs, $\sum_ip_i\,dq_i-dz$ with Reeb field
   $-\partial_z$;
3. smooth families of contact structures over $[0,1]$ that need not be
   coorientable, and Gray stability for them, with the normalization and its
   uniqueness;
4. the Legendrian neighbourhood theorem, which Tau Ceti does not have for a
   whole Legendrian submanifold.

## Decisions

`DESIGN.md` leaves one question to this file; the notes of the approving
review of #420 raise four more.

- **Smooth families of contact structures that need not be coorientable.** A
  family is a map
  `ξ : unitInterval → Π x : M, Submodule ℝ (TangentSpace I x)`, the type of
  Tau Ceti's distributions with a time parameter in front. It is a smooth
  family of contact structures, `IsContactFamily ξ`, when near every point
  of the cylinder it is the kernel of a smooth family of contact forms:

  ```lean
  def IsContactFamily (ξ : unitInterval → Π x : M, Submodule ℝ (TangentSpace I x)) :
      Prop :=
    ∀ p : unitInterval × M, ∃ α : TauCeti.SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) ℝ 1,
      ∀ᶠ q in 𝓝 p, TauCeti.IsContactFormAt (α_{q.1}).val q.2 ∧
        ξ q.1 q.2 = (α_{q.1}).kerDistribution q.2
  ```

  (with $\alpha_{q.1}$ the slice, written out as above). The local defining
  forms are global smooth forms on the cylinder that define `ξ` only near
  `p`: any local form becomes one after multiplication by a bump function,
  so nothing is lost, and the definition needs no open submanifolds. The
  neighbourhoods are taken in the cylinder, not in `M` for all times at
  once, because a non-coorientable family need not have a defining form on
  `[0, 1] × U` for a given open `U`. Each `ξ t` is then a
  `TauCeti.IsContactDistribution I ∞ (ξ t)`, so the family lies beside Tau
  Ceti's notion rather than replacing it, and a global smooth family of
  contact forms defines one (`IsContactFamily.of_isContactForm`). There is
  no separate notion for coorientable families: the global-form clause of
  the milestone takes the form and states `ξ t = (α_t).kerDistribution`.
- **Extending a non-coorientable family past the ends.** A family of
  distributions cannot be extended by Seeley's construction, which acts on
  maps into a normed space. The design never extends `ξ`. It extends the
  *Gray field* instead, through local defining forms:
  1. Near each point of `[0, 1] × M` take a defining form from
     `IsContactFamily`, extend it to `ℝ × M` by
     `DifferentialForm/TimeExtension.lean` of *Smooth families*, and restrict it to a product
     `J × U`, with `J` an open interval and `U` an open set with compact
     closure, on which every slice is contact (the contact condition is
     open, and `[0, 1]` and the closure of `U` are compact). Composing in
     time with a smooth map `ℝ → J` that is the identity on `J ∩ [0, 1]`
     shrunk slightly gives a form on `ℝ × U`, `U` as an open submanifold,
     all of whose slices are contact, to which Tau Ceti's
     `grayVectorField` applies.
  2. On `[0, 1] × U` these local Gray fields do not depend on the chosen
     form: by `eq_grayVectorField_iff`, the Gray vector at `(t, x)` is the
     unique $v\in\xi_t(x)$ with $d\alpha_t(v,w)+\dot\alpha_t(w)=0$ for
     $w\in\xi_t(x)$, and replacing $\alpha$ by $f\alpha$ with $f$
     nowhere zero multiplies this equation by $f$ (the pointwise form of
     `IsContactForm.contactMoserVectorField_of_eq_smul`; no sign of $f$ is
     needed).
     Two such forms live on `ℝ × U` and `ℝ × U'`; they are compared on
     `ℝ × (U ∩ U')` after restriction, which commutes with the Gray field
     (`tangentSpaceOpenEquiv_grayVectorField_mpullback_prodMap_subtype_val`,
     `Gray.lean`).
  3. Finitely many of the products cover `[0, 1] × M` when `M` is compact.
     Together with `ℝ × M` minus `[0, 1] × M`, on which the field is taken
     to be `0`, they form an open cover of `ℝ × M`; a smooth partition of
     unity on `ℝ × M` subordinate to it (Mathlib's
     `SmoothPartitionOfUnity.exists_isSubordinate`) glues the local Gray
     fields into a smooth time-dependent vector field `Y` on `ℝ × M`. On
     `[0, 1] × M` every summand is the Gray vector of step 2, so `Y` is
     the Gray field of `ξ` there; outside it `Y` is whatever the gluing
     gives, and nothing depends on it.
  4. `M` is compact, so the suspension of `Y` is complete
     (`TauCeti.isCompleteVectorField_timeDependentSuspensionField` with
     `K = univ`), and
     `TauCeti.timeDependentFlowDiffeotopy` makes its flow a
     `TauCeti.Diffeotopy I ∞ M`. That is the Gray isotopy.

  Only `Y` on `[0, 1] × M` enters the statements, so the choices of steps 1
  and 3 leave no trace in them.
- **Transport along the flow.** Tau Ceti's rescaling theorems for flows ask
  for the Gray equation at every point of `M` and every real time; here it
  holds only where a local form defines `ξ`. The library therefore adds the
  rescaling theorem *along one trajectory* (in
  `Geometry/Manifold/DifferentialForm/Flow/Family.lean`, below), with the
  hypothesis only at the points $(u,\varphi_{s,u}x)$, $u$ between $s$ and
  $t$; Tau Ceti has this for the invariance case
  (`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc_of_mem`)
  but not for the rescaling case. For a fixed `x`, the set of
  $t\in[0,1]$ at which $d\psi_t$ carries $\xi_0(x)$ onto
  $\xi_t(\psi_tx)$ is open and closed in `[0, 1]`: near any
  $(t_0,\psi_{t_0}x)$ one local defining form serves for all nearby times,
  and the trajectory lemma with the cocycle `TauCeti.timeDependentFlowOf_trans`
  moves the property from $t_0$ to nearby $t$ and back. It contains `0`, so
  it is `[0, 1]`.
- **Uniqueness, checked against `eq_grayVectorField_iff` after
  reparametrization.** Let `Φ` be a diffeotopy that transports `ξ` and whose
  velocity lies in `ξ`. Read it over `ℝ` as $\psi_t=\Phi_{s(t)}$ with
  $s=$ `Real.smoothTransition`, by `Diffeotopy/Real.lean` of *Smooth families*;
  its `TauCeti.eulerianField` is $Z_t=s'(t)X_{s(t)}$, where $X$ is the
  velocity of `Φ`, and $\psi$ is the time-dependent flow of $Z$
  (`TauCeti.timeDependentFlowOf_eulerianField`). Near a point, with a local
  defining form $\alpha$, the reparametrized family $\alpha_{s(t)}$ has time
  derivative $s'(t)\dot\alpha_{s(t)}$. Differentiating
  $\psi_t^*\alpha_{s(t)}\in C^\infty\cdot\alpha_0$ with
  `TauCeti.hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk`, and
  using that $\alpha_{s(t)}(Z_t)=0$ on an open set (so Cartan's formula has
  no exact term), gives
  $\bigl(\iota_{Z_t}d\alpha_{s(t)}+s'(t)\dot\alpha_{s(t)}\bigr)|_{\xi}=0$.
  So $Z_t$ solves the equation of `eq_grayVectorField_iff` for the
  reparametrized family, whose solution is $s'(t)Y_{s(t)}$ because the
  equation is linear in the time derivative. Hence $\psi$ and
  $t\mapsto G_{s(t)}$, for the Gray isotopy $G$, are flows of the same field
  $s'(t)Y_{s(t)}$, and agree by `TauCeti.timeDependentFlowOf_eq_of_hasMFDerivAt`.
  As $s$ maps `ℝ` onto `[0, 1]`, $\Phi=G$. At $t\le0$ and $t\ge1$ both sides
  of the equation vanish, so the argument never needs $X$ at the ends of the
  interval separately.
- **The velocity of a diffeotopy** in the statements is read along the
  motion, as Tau Ceti's `TauCeti.Diffeotopy.HasHamiltonian` reads it:
  `mfderiv (I.prod (𝓡∂ 1)) I Φ.cylinderMap (x, t) ((0 : E), (1 : TangentSpace (𝓡∂ 1) t))`,
  a vector at `Φ (t, x)`. This is $\dot\psi_t\circ\psi_t^{-1}$ evaluated at
  $\psi_t(x)$, so the normalization $X_t\in\xi_t$ is a condition on this
  vector, and it does not depend on how *Hamiltonian flows* chooses to
  read velocities in its own statements.
- **The Legendrian neighbourhood theorem: the hypersurface route.** The
  relative Gray theorem
  `TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq_smul_of_apply_eq`
  (`Interpolation.lean`) gives, from forms agreeing to first order along
  $L$, only $\Phi^*\alpha=g\alpha_0$ with $g>0$. Turning that into equality
  needs the strict Moser step of `StrictMoser.lean`, whose Reeb-direction
  equation is an ODE along the Reeb flow that Tau Ceti takes as a
  hypothesis; and the first-order agreement itself needs a diffeomorphism
  with prescribed derivative along $L$. The page's route needs neither and
  gives equality at once, so the design follows it:
  1. *A hypersurface through `L` tangent to `ξ`, parametrized by `T*L`.* The
     map $[w]\mapsto\bigl(d\alpha(df\,\cdot,w),\ \alpha(w)\bigr)$,
     $\nu_q\to T_q^*L\times\mathbb R$, on the normal space
     $\nu_q=T_{f(q)}M/df(T_qL)$, is well defined and injective (its kernel
     consists of the classes of $w\in\xi\cap(df\,T_qL)^{d\alpha}=df\,T_qL$,
     because $L$ is Legendrian), hence bijective by dimension; these maps
     form a smooth bundle isomorphism, by Tau Ceti's
     `TauCeti.SmoothEmbedding.contMDiff_normalBundle_iff` and
     `TauCeti.contMDiff_bundle_symm`, as in Tau Ceti's
     `TauCeti.SmoothEmbedding.normalBundleDiffeomorphOfIsLagrangianMap`, and
     its inverse restricted to $T_q^*L\times\{0\}$ is a smooth, fibrewise
     linear, injective bundle map $j:T^*L\to\nu$. The tubular map is not the
     diffeomorphism of `TauCeti.SmoothEmbedding.exists_diffeomorph_normalBundle_subset`,
     whose derivative along the zero section Tau Ceti does not state: it is
     the normal exponential of an auxiliary metric
     (`TauCeti.SmoothEmbedding.exists_partialDiffeomorph_normalExp_subset`,
     with derivative from `TauCeti.SmoothEmbedding.mfderiv_normalExp_zeroSection_apply`),
     precomposed with a radial compression
     `TauCeti.vectorBundleRadialPartialDiffeomorphOfRadius` into its domain,
     a smooth injective $\Psi:\nu\to M$ with $\Psi\circ0=f$ whose derivative
     on the vertical vector $v$ at $0_q$ has class $c(q)\,v$, $c(q)>0$
     (`TauCeti.SmoothEmbedding.exists_contMDiff_injective_normalBundle`, in
     `Geometry/Manifold/TubularNeighborhood/Riemannian/Injective.lean`). The
     map $\iota=\Psi\circ j:T^*L\to M$ is injective, sends $0_q$ to $f(q)$,
     and its differential at $0_q$ is an isomorphism onto $\xi_{f(q)}$
     (horizontal part $df$, vertical part in $\xi$, dimension $2n$; read
     through `TauCeti.Bundle.zeroSectionTangentEquiv`). So on an open
     neighbourhood $N$ of the zero section it is an immersion transverse to
     the Reeb field (openness by
     `ContMDiffAt.eventually_injective_mfderiv_and_notMem_range`, in
     `Geometry/Manifold/Immersion/Transverse.lean`), and
     `IsContactForm.nondegenerate_bilinFormAt_mextDerivₗ_mpullback` makes
     $-d(\iota^*\alpha)$ nondegenerate there. The zero section is
     Lagrangian for it, since $\iota^*\alpha$ vanishes on its tangent
     vectors.
  2. *The Lagrangian neighbourhood theorem* of *Symplectic neighbourhoods*
     (`Lagrangian.lean`), applied on the open submanifold $N$ with the
     symplectic form $-d\beta$, $\beta=\iota^*\alpha$, gives a map $\theta$ into $N$, defined near the zero
     section of $T^*L$ and the identity on it, with $\theta^*(-d\beta)=\omega_{\mathrm{can}}=-d\lambda_{\mathrm{can}}$.
  3. *A relative primitive.* The difference $\theta^*\beta-\lambda_{\mathrm{can}}$
     has zero exterior derivative and vanishes on the zero section (for $\lambda_{\mathrm{can}}$,
     by Tau Ceti's `TauCeti.CotangentBundle.isExactLagrangianMap_zeroSection`),
     so `TauCeti.SmoothEmbedding.exists_isSmoothForm_relative_primitive`
     gives $g$ with $dg=\theta^*\beta-\lambda_{\mathrm{can}}$ and $g=0$ on
     the zero section.
  4. *The Reeb flow.* $\Phi(a,z)=\varphi^{R}_{-z-g(a)}(\iota\theta(a))$.
     `TauCeti.mpullback_flowOf_comp_apply_eq_contactization` gives
     $(t,a)\mapsto\varphi^R_t(\iota\theta a)$ the pullback
     $dt+\theta^*\beta$; composing with $(a,z)\mapsto(a,-z-g(a))$ gives
     $\lambda_{\mathrm{can}}-dz$. It is a local diffeomorphism near the zero
     section (`isLocalDiffeomorphAt_flowOf_reebVectorField_comp`), and it is
     $f$ on the zero section, which `f` embeds; Tau Ceti's
     `IsLocalHomeomorphOn.exists_isOpenEmbedding_near_section`, which
     assumes no compactness or closedness of the section, restricts it to an
     open embedding on some open set around the zero section, so a diffeomorphism
     onto an open neighbourhood of $f(L)$.

  Nothing in this route uses that `L` is properly embedded: the tubular
  neighbourhood, the relative primitive and the injectivity lemma hold for
  any embedding. The milestone is therefore stated without that hypothesis,
  which is more general than the page; if `Lagrangian.lean` of *Symplectic
  neighbourhoods* asks for a closed image, the zero section of `T*L` has
  one, so step 2 still applies.
- **Statements in the page's signs.** As `DESIGN.md`'s table says, the
  standard form $\sum_ip_i\,dq_i-dz$ is `TauCeti.innerProductContactForm`
  pulled back by $\sigma(q,p,z)=(q,-p,-z)$, which is
  `(ContinuousLinearEquiv.refl ℝ V).prodCongr (ContinuousLinearEquiv.neg ℝ)`
  on `V × (V × ℝ)`, $V=$ `EuclideanSpace ℝ (Fin n)`; it is written in the
  statements evaluated at $\sigma$, with no new definition. Its Reeb field
  is $-\partial_z$, the vector `(0, 0, -1)`. The model of the Legendrian
  neighbourhood theorem, $\lambda_{\mathrm{can}}-dz$ on
  $T^*L\times\mathbb R$, is
  `-(TauCeti.CotangentBundle.liouvilleForm J L).contactization`.
- **Contact Hamiltonian flows over `ℝ`.** The rescaling formula is about the
  maximal flow of a time-dependent Hamiltonian, wherever it is defined.
  Tau Ceti's maximal time-dependent flow `TauCeti.timeDependentFlowOf`,
  with its domain `TauCeti.timeDependentFlowDomain`, is over `ℝ`, and a
  `Diffeotopy` over `[0, 1]` cannot express "wherever defined". So this one
  family statement is made over `ℝ`, for `H : ℝ × M → ℝ` smooth; a
  Hamiltonian over `[0, 1]` enters through its extension by
  `ContMDiff/TimeExtension.lean`. `DESIGN.md`'s convention on families records the
  exception.
- **Namespaces.** Definitions and theorems about Tau Ceti's objects go in
  their namespaces (`TauCeti.SmoothForm`, `TauCeti.SmoothForm.IsContactForm`,
  `TauCeti.Diffeotopy`, `TauCeti.IsLegendrianEmbedding`), so that dot
  notation finds them and they can move to Tau Ceti unchanged, as
  `TauCeti.SmoothTwoForm.symplecticVectorFields` sits beside
  `TauCeti.SmoothTwoForm`. The one new notion with a type of this library's
  own, `IsContactFamily`, is in `SymplecticGeometry`.
- **Credit for the errata.** None of the four milestones, as the page states
  them, follows a statement that [McDuffSalamon2019Errata] corrects. If a
  building issue adds a result that does (for instance the positive
  rescaling of Proposition 3.5.1(iii), which needs a coorientation), its
  docstring cites the errata.

## Files and declarations

### `Geometry/Manifold/DifferentialForm/Flow/Family.lean`

Named like Tau Ceti's file, in the namespace `TauCeti`. Two theorems. The
first is the rescaling form of Moser's principle along a single trajectory:

```lean
theorem mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_forall_mem_uIcc_of_mem
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2 (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {s t : ℝ} {x : M} (h : ((s, t), x) ∈ timeDependentFlowDomain X)
    (hα : ∀ u ∈ uIcc s t, ContMDiffAt … 1 (fun p ↦ TotalSpace.mk' _ p (α p)) (u, timeDependentFlowOf X s u x))
    {c : ℝ → ℝ} (hc : ContinuousOn c (uIcc s t))
    (hL : ∀ u ∈ uIcc s t, (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u)
          (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α) +
        mlieDerivForm (X u) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u) α))
          (timeDependentFlowOf X s u x) =
        c u • mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u) α (timeDependentFlowOf X s u x)) :
    mpullback I I (timeDependentFlowOf X s t) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α) x =
      Real.exp (∫ u in s..t, c u) • mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) α x
```

with Tau Ceti's variables of that file (`α : RoughForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F k`).
The proof is that of Tau Ceti's
`mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_mem`
with the hypothesis read only along the trajectory, through
`hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk`, as Tau Ceti's
`…_apply_eq_of_forall_mem_uIcc_of_mem` does for the invariance case; the
module docstring credits both. The rate `c` is a function of time only,
because along one trajectory nothing else is needed. Expected size: 100
lines.

The second, added by *Hamiltonian flows* for `PoissonAlgebra.lean`, under
the same `[IsManifold I 2 M]`, is Tau Ceti's
`mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_mem` for the
constant family of a closed form whose contractions are closed:

```lean
theorem mpullback_timeDependentFlowOf_apply_of_mextDeriv_interior_eq_zero
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2 (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {β : SmoothForm I M F (k + 1)} (hβ : β.IsClosed)
    (hXβ : ∀ t, mextDeriv (RoughForm.interior (X t) β.val) = 0)
    {s t : ℝ} {x : M} (h : ((s, t), x) ∈ timeDependentFlowDomain X) :
    mpullback I I (timeDependentFlowOf X s t) β.val x = β.val x
```

The file also has, in `TauCeti.SmoothForm`, the slices of a pullback along
`Prod.map id f`: `mpullback_prodMk_mpullback_prodMap`
($\iota_t^*(\mathrm{id}\times f)^*\alpha=f^*\iota_t^*\alpha$) and
`mpullback_prodMk_timeDeriv_mpullback_prodMap` (the same for
`timeDeriv`, by uniqueness of the derivative of $u\mapsto f^*\alpha_u$).
`Gray.lean` uses them.

### `Geometry/Contact/Hamiltonian.lean`

Named like Tau Ceti's file, in `TauCeti.SmoothForm`.

- `contactVectorFields (α : SmoothForm I M ℝ 1) : Submodule ℝ Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯`,
  the smooth fields `X` with `∃ g : M → ℝ, mlieDerivForm X α.val = fun x ↦ g x • α.val x`,
  beside Tau Ceti's `TauCeti.SmoothTwoForm.symplecticVectorFields` (closure
  under sums by `TauCeti.mlieDerivForm_add`); `@[simp] mem_contactVectorFields_iff`.
  The multiplier `g` may vanish; no smoothness of `g` is asked, since for a
  contact form it is forced:
- `IsContactForm.mem_contactVectorFields_iff_mlieDerivForm_eq (hα) :
  X ∈ α.contactVectorFields ↔ mlieDerivForm X α.val = fun x ↦
  mvfderiv I (fun y ↦ α.val y ![X y]) x (α.reebVectorField x) • α.val x`,
  from `eq_mvfderiv_reebVectorField_of_mlieDerivForm_apply_eq_smul`.
- `IsContactForm.mem_contactVectorFields_iff_kerDistribution_mpullback_flowOf`
  (`[I.Boundaryless] [T2Space M]`): `X ∈ α.contactVectorFields` exactly when,
  for every `(t, x)` in `flowDomain X`,
  `RoughForm.ker (TauCeti.mpullback I I (flowOf X t) α.val) x = α.kerDistribution x`,
  that is, the local flow maps the contact hyperplanes to contact hyperplanes.
  Forward: `IsContactHamiltonianVectorField.mpullback_flowOf_apply` for the
  Hamiltonian `α(X)`, whose multiplier is positive. Backward: the pullback at
  `x` is $c(t)\,\alpha_x$ with $c(t)$ its value on $R_x$; differentiate at
  `t = 0` with `TauCeti.hasDerivAt_mpullback_flowOf_zero`, so
  $(\mathcal L_X\alpha)_x=c'(0)\alpha_x$.
- `IsContactForm.contactHamiltonianEquiv (hα) : α.contactVectorFields ≃ₗ[ℝ] C^∞⟮I, M; ℝ⟯`,
  $X\mapsto\alpha(X)$, with inverse $H\mapsto X_H$
  (`contactHamiltonianVectorField`, smooth by
  `IsContactForm.contMDiff_contactHamiltonianVectorField`, contact by
  `IsContactHamiltonianVectorField.mlieDerivForm_eq`, and the two-sided
  inverse by `isContactHamiltonianVectorField_iff_mlieDerivForm` and
  `isContactHamiltonianVectorField_iff_eq`). API:
  `@[simp] contactHamiltonianEquiv_apply` (`(e X) x = α.val x ![X x]`) and
  `@[simp] coe_contactHamiltonianEquiv_symm_apply`
  (`⇑(e.symm H) = α.contactHamiltonianVectorField H`).
- `IsContactForm.reebVectorField_eq_contactHamiltonianVectorField_of_eq_smul`:
  for `H` smooth and nowhere zero and `β` with
  `∀ x, β.val x = (H x)⁻¹ • α.val x`, `β.IsContactForm` and
  `β.reebVectorField = α.contactHamiltonianVectorField H`; from
  `isContactForm_iff_of_eq_smul`, `contactHamiltonianVectorField_of_eq_smul`
  with $u=H^{-1}$, $f=H$, and `contactHamiltonianVectorField_one` for `β`.
- `IsContactForm.preservesCoorientation_refl_iff_pos` for the same `β`:
  `(Diffeomorph.refl I M ∞).PreservesCoorientation α β ↔ ∀ x, 0 < H x`, Tau
  Ceti's notion of "the same coorientation".
- `contMDiff_contactHamiltonianVectorField_prodMk (hα) (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞ H)`:
  the time-dependent field `(t, y) ↦ X_{H_t}(y)`, with
  $H_t=$ `fun y ↦ H (t, y)`, is jointly smooth as a map `ℝ × M → TM`. Tau
  Ceti proves smoothness only for one function; the proof follows
  `TauCeti.SmoothForm.contMDiffAt_sectionAlong_contactMoserVectorField`
  (inverse contact flat map along a parameter), which the docstring credits.
- `IsContactForm.mpullback_timeDependentFlowOf_contactHamiltonianVectorField_apply`
  (`[I.Boundaryless] [T2Space M]`): writing
  `X t := α.contactHamiltonianVectorField (fun y ↦ H (t, y))`, for every
  `((0, t), x) ∈ timeDependentFlowDomain X`,
  `TauCeti.mpullback I I (timeDependentFlowOf X 0 t) α.val x =
   Real.exp (∫ s in 0..t, mvfderiv I (fun y ↦ H (s, y)) (timeDependentFlowOf X 0 s x)
     (α.reebVectorField (timeDependentFlowOf X 0 s x))) • α.val x`.
  From Tau Ceti's
  `mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_mem`
  for the constant family `mpullback Prod.snd α` (time derivative `0`), with
  $g(t,y)=R(H_t)(y)$ and Gray's equation given by
  `IsContactHamiltonianVectorField.mlieDerivForm_eq`.
- **Milestone theorem** `IsContactForm.contactVectorFields_correspondence (hα)`,
  the conjunction of: the two characterizations of `contactVectorFields`
  above; for every `H : C^∞⟮I, M; ℝ⟯`, that `(e.symm H : Π x, _)` is the
  unique field `X` with `IsContactHamiltonianVectorField α H X`, that
  `mlieDerivForm` of it is `R(H) • α`, and `X_1 = R`; the rescaling
  formula; and, for nowhere zero `H`, transversality
  (`IsContactHamiltonianVectorField.mem_kerDistribution_iff`), the Reeb field
  of `α/H` and the coorientation clause. Milestone: *Contact vector fields
  and contact Hamiltonians*.

Expected size: 450 lines, in two issues (H1 and H2 below).

### `Geometry/Contact/Darboux/Strict.lean`

Named like Tau Ceti's file, in `TauCeti.SmoothForm.IsContactForm` and
`TauCeti.IsContactDistribution`, with `[I.Boundaryless] [T2Space M]` as in
Tau Ceti's file, `V = EuclideanSpace ℝ (Fin n)` and `σ` as above.

- `IsContactForm.exists_strictDarbouxChart_reebVectorField_of_finrank_eq
  (hα) (hn : finrank ℝ E = 2 * n + 1) (x₀ : M)`:

  ```lean
  ∃ chart : PartialDiffeomorph I 𝓘(ℝ, V × V × ℝ) M (V × V × ℝ) ∞,
    x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
    (∀ x ∈ chart.source, ∀ v : TangentSpace I x,
      (innerProductContactForm V).val (σ (chart x)) ![σ (mvfderiv I _ chart x v)] =
        α.val x ![v]) ∧
    (∀ x ∈ chart.source, mvfderiv I _ chart x (α.reebVectorField x) = (0, 0, -1)) ∧
    ∀ x ∈ chart.source, α.kerDistribution x =
      ((innerProductContactForm V).kerDistribution (σ (chart x))).comap
        (σ.toLinearMap ∘ₗ (mfderiv I _ chart x).toLinearMap)
  ```

  The chart is Tau Ceti's strict chart followed by
  `σ.toDiffeomorph.toPartialDiffeomorph` (`PartialDiffeomorph.trans`); the
  form identity holds because $\sigma$ is an involution. The Reeb clause:
  the chart is a strict contactomorphism on its source, so it carries $R_\alpha$
  to the Reeb field of the standard form, $-\partial_z$, by
  `eq_reebVectorField_iff` read through the chart (restricted to its source
  as an open submanifold, where it is a diffeomorphism onto the target and
  `Diffeomorph.IsStrictContactomorphism.mfderiv_reebVectorField` applies).
  The last clause, the kernels, follows from the first. Milestone: *Contact
  Darboux theorem*.
- `IsContactDistribution.exists_darbouxChart_comap_of_finrank_eq
  (hD : IsContactDistribution I ∞ D) (hn) (x₀)`: the same chart property for a
  contact structure that need not be the kernel of a form,
  `D x = (ker of the standard form at σ (chart x)).comap (σ ∘ dchart)`, from
  Tau Ceti's `IsContactDistribution.exists_darbouxChart` by `σ`. This is the
  page's "consequently" for structures without a defining form.

Expected size: 200 lines.

### `Geometry/Contact/Levi.lean`

Named like Tau Ceti's file, in Tau Ceti's namespaces.

- `TauCeti.IsContMDiffDistribution.of_forall_eventuallyEq_kerDistribution`:
  a distribution that near each `x` is the kernel of a smooth one-form `β`
  with `β_x ≠ 0` is `C^n` of rank `finrank ℝ E - 1`; the local form of
  `TauCeti.SmoothForm.isContMDiffDistribution_kerDistribution`.

### `Geometry/Contact/Moser.lean`

Named like Tau Ceti's file, in Tau Ceti's namespaces.

- `TauCeti.SmoothForm.IsContactForm.contactMoserVectorField_apply_of_eventuallyEq_smul`:
  the pointwise form of `IsContactForm.contactMoserVectorField_of_eq_smul`,
  for contact forms with `α' = f α` near `x`, `f` differentiable and
  nonzero at `x`, and `β'_x = f(x) β_x + c α_x`.
- `TauCeti.SmoothForm.IsContactForm.mfderiv_contactMoserVectorField_mpullback (hα) (f) (hf) (hdf) (β) (x)`:
  for a contact form `α` and `f` smooth with bijective differentials,
  `mfderiv I J f x ((mpullback f hf α).contactMoserVectorField (mpullback f hf β) x) = α.contactMoserVectorField β (f x)`;
  the proof of Tau Ceti's `IsContactForm.mfderiv_reebVectorField_mpullback`,
  through `eq_contactMoserVectorField_iff`.
- `TauCeti.SmoothForm.IsContactForm.tangentSpaceOpenEquiv_contactMoserVectorField_mpullback_subtype_val`:
  the case of an open subset, with `TauCeti.Manifold.tangentSpaceOpenEquiv`.

### `Geometry/Contact/Family.lean`

Named like Tau Ceti's file, in `SymplecticGeometry`.

- `IsContactFamily ξ` as in *Decisions*, with `isContactFamily_def` and
  `isContactFamily_iff` (the kernels read on vertical vectors `(0, v)`).
- `IsContactFamily.of_isContactForm`: if every slice of
  `α : SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) ℝ 1` is a contact
  form, then `IsContactFamily fun t ↦ (α_t).kerDistribution`. This is the
  example of the predicate and the input of the global-form clause.
- `IsContactFamily.isContactDistribution (hξ) (t) : TauCeti.IsContactDistribution I ∞ (ξ t)`,
  from `TauCeti.isContactDistribution_iff_forall_exists_isContactFormAt` and
  `TauCeti.IsContMDiffDistribution.of_forall_eventuallyEq_kerDistribution`
  (`Geometry/Contact/Levi.lean`) applied to the slices of local defining
  forms.
- `IsContactFamily.exists_local_extension (hξ) [CompactSpace M] (p)`: step 1
  of the extension in *Decisions*. For every `p : unitInterval × M` there
  are an open interval `J ∋ p.1`, an open `U ∋ p.2` with compact closure, and
  `α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1` (on the open submanifold `U`)
  all of whose slices are contact, with `ξ t x = (α_t).kerDistribution x`
  for `t ∈ J ∩ [0, 1]`, `x ∈ U`. Uses `DifferentialForm/TimeExtension.lean` of
  *Smooth families* and a smooth reparametrization `ℝ → J` that is the identity on
  a neighbourhood of the relevant times.
- `TauCeti.SmoothForm.grayVectorField_eq_of_eventuallyEq_smul` (`[I.Boundaryless]`):
  the pointwise independence of step 2, for two families on `ℝ × M` with
  contact slices at `t ∈ s`, `UniqueDiffWithinAt ℝ s t` (`s = [0, 1]` in
  use), whose slices are related by `α'_u = f(u, ·) α_u` on
  `𝓝[s ×ˢ univ] (t, x)`, with `f (t, x) ≠ 0`, `f` differentiable within
  `s` in time at `t` and in space at `x`. It is about Tau Ceti's
  `grayVectorField`, hence in its namespace, and follows from the pointwise
  form of `IsContactForm.contactMoserVectorField_of_eq_smul`,
  `TauCeti.SmoothForm.IsContactForm.contactMoserVectorField_apply_of_eventuallyEq_smul`,
  in `Geometry/Contact/Moser.lean`.

Expected size: 400 lines, in two issues (G1 and G2).

### `Geometry/Contact/Gray.lean`

Named like Tau Ceti's file. With `[I.Boundaryless] [T2Space M] [CompactSpace M]`.

- First, in `TauCeti.SmoothForm`, with `[I.Boundaryless]` only:
  `mfderiv_grayVectorField_mpullback_prodMap (hc) (f) (hf) (hdf) (x)`, for
  `α` on `ℝ × N` whose slice at `t` is contact and `f` smooth with bijective
  differentials,
  `mfderiv I J f x ((mpullback (Prod.map id f) _ α).grayVectorField t x) = α.grayVectorField t (f x)`,
  from the slice lemmas of `Flow/Family.lean` and
  `mfderiv_contactMoserVectorField_mpullback`; and
  `tangentSpaceOpenEquiv_grayVectorField_mpullback_prodMap_subtype_val`, the
  case of an open subset `U`, which compares local Gray fields on different open sets in
  step 2 of *Decisions*.
- `TauCeti.Diffeotopy.Transports (Φ : Diffeotopy I ∞ M) (ξ : unitInterval → Π x, Submodule ℝ (TangentSpace I x)) : Prop`,
  `∀ t x, ξ 0 x = (ξ t (Φ (t, x))).comap (mfderiv I I (Φ.timeSlice t) x).toLinearMap`,
  the condition $\psi_t^*\xi_t=\xi_0$ written as Tau Ceti writes pullbacks of
  distributions (`IsContactDistribution.exists_darbouxChart`), with
  `transports_iff`, `Transports.trans` (if `χ` transports the constant family
  `fun _ ↦ ξ 0` and `Φ` transports `ξ`, then `χ.trans Φ`, which is
  $\psi_t\circ\chi_t$ by `TauCeti.Diffeotopy.trans_apply`, transports `ξ`:
  the non-uniqueness the page mentions without the normalization) and
  `transports_refl` for a constant family.
- `IsContactFamily.exists_grayField (hξ)`: a time-dependent field
  `Y : ℝ → Π x, TangentSpace I x`, jointly smooth on `ℝ × M`, with, for
  `t ∈ [0, 1]`, `Y t x ∈ ξ t x` and the Gray equation against every local
  defining family near `(t, x)`; step 3 of *Decisions*, by a smooth partition
  of unity on `ℝ × M`.
- `IsContactFamily.grayDiffeotopy (hξ) : Diffeotopy I ∞ M`, the
  `TauCeti.timeDependentFlowDiffeotopy` of the field chosen by
  `exists_grayField` (complete since `M` is compact), with
  `IsContactFamily.transports_grayDiffeotopy` (the clopen argument of
  *Decisions*, through the trajectory theorem of `Flow/Family.lean`) and
  `IsContactFamily.velocity_grayDiffeotopy_mem` (its velocity is `Y`, in `ξ`).
  The definition is a choice; only the existence and uniqueness below are
  meant to be used.
- `IsContactFamily.eq_grayDiffeotopy_of_transports (hξ) (hΦ : Φ.Transports ξ)
  (hv : ∀ t x, velocity ∈ ξ t (Φ (t, x))) : Φ = hξ.grayDiffeotopy`, the
  uniqueness argument of *Decisions*, through the reading of `Φ` over `ℝ` by
  `Real.smoothTransition` in `Diffeotopy/Real.lean` of *Smooth families*.
- `TauCeti.Diffeotopy.Transports.exists_mpullback_eq_smul
  (α : SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) ℝ 1) (hc : ∀ t, (α_t).IsContactForm)
  (hΦ : Φ.Transports fun t ↦ (α_t).kerDistribution)`:
  `∃ f : unitInterval × M → ℝ, ContMDiff ((𝓡∂ 1).prod I) 𝓘(ℝ) ∞ f ∧ (∀ p, 0 < f p) ∧
   (∀ x, f (0, x) = 1) ∧ ∀ t x, (mpullback (Φ.timeSlice t) _ α_t).val x = f (t, x) • (α_0).val x`.
  It holds for every transporting diffeotopy, not only the normalized one,
  and needs no compactness: $f(t,x)$ is the pullback evaluated on
  $R_{\alpha_0}(x)$, smooth jointly, nowhere zero, `1` at `t = 0`, hence
  positive since `[0, 1]` is connected. As a corollary each
  `Φ.timeSlice t` satisfies `Diffeomorph.PreservesCoorientation` from
  $\alpha_0$ to $\alpha_t$.
- **Milestone theorem** `IsContactFamily.existsUnique_transports (hξ)`:

  ```lean
  (∃! Φ : Diffeotopy I ∞ M, Φ.Transports ξ ∧ ∀ (t : unitInterval) (x : M),
      mfderiv (I.prod (𝓡∂ 1)) I Φ.cylinderMap (x, t)
        ((0 : E), (1 : TangentSpace (𝓡∂ 1) t)) ∈ ξ t (Φ (t, x))) ∧
    ∀ α, (∀ t, (α_t).IsContactForm) → (∀ t, ξ t = (α_t).kerDistribution) →
      ∀ Φ : Diffeotopy I ∞ M, Φ.Transports ξ → ∃ f, (the clause above)
  ```

  Milestone: *Gray stability*.

Expected size: 550 lines, in two issues (G3 and G4), after the naturality
lemmas of N.

### `Geometry/Contact/LegendrianNeighborhood.lean`

In `TauCeti.IsLegendrianEmbedding`. `L` is a boundaryless manifold modelled
on `J : ModelWithCorners ℝ E' H'`, `f : L → M` with
`hf : TauCeti.IsLegendrianEmbedding J α.kerDistribution f`, `M` is
boundaryless and Hausdorff, and both are second countable.

- `IsLegendrianEmbedding.exists_contactSlice (hα) (hf)`: step 1 of the route.
  A smooth injective map `ι : CotangentBundle J L → M` and an open
  neighbourhood `N` of the range of the zero section with `ι (0_q) = f q`, the
  differential of `ι` at each point of `N` injective with range transverse to
  `α.reebVectorField`, and at `0_q` with range `α.kerDistribution (f q)`.
  Public, since the isotropic neighbourhood theorem of a later page builds
  its slice the same way. It uses Tau Ceti's normal exponential, normal
  bundle and zero-section splitting, and the openness of immersions
  transverse to a vector field,
  `ContMDiffAt.eventually_injective_mfderiv_and_notMem_range`, which it adds
  in `Geometry/Manifold/Immersion/Transverse.lean` (beside Tau Ceti's
  `ContMDiffAt.eventually_injective_mfderiv`), and the smooth injective map
  of the normal bundle
  `TauCeti.SmoothEmbedding.exists_contMDiff_injective_normalBundle`, which it
  adds in `Geometry/Manifold/TubularNeighborhood/Riemannian/Injective.lean`
  (mirroring Tau Ceti's `TubularNeighborhood/Riemannian/`).
- **Milestone theorem**
  `IsLegendrianEmbedding.exists_diffeomorph_opens_mpullback_eq_neg_contactization (hα) (hf)`:

  ```lean
  ∃ (U : Opens (CotangentBundle J L × ℝ)) (V : Opens M) (Φ : U ≃ₘ⟮(J.prod 𝓘(ℝ, E' →L[ℝ] ℝ)).prod 𝓘(ℝ), I⟯ V),
    (∀ q, ∃ h : (Bundle.zeroSection _ _ q, (0 : ℝ)) ∈ U, (Φ ⟨_, h⟩ : M) = f q) ∧
    SmoothForm.mpullback Φ Φ.contMDiff (SmoothForm.mpullback (Subtype.val : V → M) contMDiff_subtypeVal α) =
      -SmoothForm.mpullback (Subtype.val : U → _) contMDiff_subtypeVal
        (CotangentBundle.liouvilleForm J L).contactization
  ```

  in the form of the neighbourhood germs of *Manifolds, families and signs*
  (that of `TauCeti.SmoothTwoForm.exists_diffeomorph_opens_of_eq_along`),
  by steps 2–4 of the route. No properness hypothesis (see *Decisions*).
  Milestone: *Legendrian neighbourhood theorem*.

Expected size: 650 lines, in two issues (L1 and L2).

## What the part uses from other parts

- *Smooth families* (#466, #467):
  `Geometry/Manifold/DifferentialForm/TimeExtension.lean`, the extension of
  a smooth form on `unitInterval × M` to `ℝ × M` (for
  `IsContactFamily.exists_local_extension`); and
  `Geometry/Diffeomorphism/Diffeotopy/Real.lean`, the reading of a
  `Diffeotopy` $\Phi$ over `ℝ` as $\Phi_{s(t)}$, $s=$ `Real.smoothTransition`,
  with `TauCeti.eulerianField` $s'(t)X_{s(t)}$, where $X$ is the velocity
  along the motion as read above (for the uniqueness). If that file reads
  velocities differently, the uniqueness issue converts with the lemma
  relating the two readings, which `Diffeotopy/Real.lean` provides.
- *Symplectic neighbourhoods* (#475, #476): the Lagrangian neighbourhood
  theorem of `Geometry/Symplectic/Neighborhood/Lagrangian.lean`, for a
  Lagrangian embedding into a symplectic manifold, with model
  $-d\lambda_{\mathrm{can}}$ on `T*L` and a map fixing the zero section; it
  is applied on an open submanifold of `T*L`.
- *Cotangent bundles* (#470) only through Tau Ceti: the zero section and
  `TauCeti.Bundle.zeroSectionTangentEquiv`. The part does not need the
  library's `ZeroSection.lean`.

Mathlib and Tau Ceti were searched, at the pinned versions, for the notions
this part defines (a submodule of contact vector fields, an equivalence with
functions, families of contact distributions, transport of distributions by a
diffeotopy, time-dependent contact Hamiltonian flows, Legendrian
neighbourhoods); neither has them. The correspondence list of
`atlas/symplectic-manifolds-lean.md` for §3.5 names the Tau Ceti declarations
used above and confirms that the bundled bijection, the non-coorientable Gray
theorem, the interval-indexed Gray theorem and the whole-Legendrian
neighbourhood are missing.

## Building issues

In this order; each is blocked by the ones listed, and all are sub-issues of
#478 (*Build the part Contact geometry*). Sizes are estimates.

| # | Issue | Files | Blocked by | Size |
|---|---|---|---|---|
| H1 | Contact vector fields and their equivalence with functions | `Geometry/Contact/Hamiltonian.lean` (`contactVectorFields`, the two characterizations, `contactHamiltonianEquiv`, the Reeb field of `α/H` and its coorientation) | — | 300 |
| H2 | Time-dependent contact Hamiltonians and the milestone | `Geometry/Contact/Hamiltonian.lean` (joint smoothness, rescaling formula, `contactVectorFields_correspondence`) | H1 | 200 |
| D | The contact Darboux theorem in the page's signs | `Geometry/Contact/Darboux/Strict.lean` | — | 200 |
| G0 | Moser's principle along one trajectory, rescaling case | `Geometry/Manifold/DifferentialForm/Flow/Family.lean` | — | 100 |
| G1 | Smooth families of contact structures | `Geometry/Contact/Family.lean` (`IsContactFamily` and its API, `grayVectorField_eq_of_eventuallyEq_smul`), `Geometry/Contact/Levi.lean` (`of_forall_eventuallyEq_kerDistribution`), `Geometry/Contact/Moser.lean` (`contactMoserVectorField_apply_of_eventuallyEq_smul`) | — | 250 |
| G2 | Local defining families over `ℝ` | `Geometry/Contact/Family.lean` (`exists_local_extension`) | G1, the issue of *Smooth families* that adds `DifferentialForm/TimeExtension.lean` | 150 |
| N | Naturality of the contact-Moser and Gray vectors under pullback and restriction to open subsets (#598) | `Geometry/Contact/Moser.lean`, `Geometry/Contact/Gray.lean` (`mfderiv_grayVectorField_mpullback_prodMap`), the slice lemmas of `Flow/Family.lean` | — | 150 |
| G3 | The Gray field and the Gray isotopy of a family | `Geometry/Contact/Gray.lean` (`Transports`, `exists_grayField`, `grayDiffeotopy`, transport and velocity) | G0, G2, N | 350 |
| G4 | Uniqueness, rescaling of forms, and Gray stability | `Geometry/Contact/Gray.lean` (`eq_grayDiffeotopy_of_transports`, `Transports.exists_mpullback_eq_smul`, the milestone) | G3, the issue of *Smooth families* that adds `Diffeotopy/Real.lean` | 250 |
| L1 | A slice through a Legendrian submanifold | `Geometry/Contact/LegendrianNeighborhood.lean` (`exists_contactSlice`) | — | 300 |
| L2 | The Legendrian neighbourhood theorem | `Geometry/Contact/LegendrianNeighborhood.lean` (the milestone) | L1, the issue of *Symplectic neighbourhoods* that adds `Lagrangian.lean` | 350 |

H1, D, G0, G1, N and L1 can start at once. While the issues of *Smooth
families* and *Symplectic neighbourhoods* that add the files named do not
exist yet, G2, G4 and L2 are blocked by those parts' building issues, #467
and #476. The milestones are proved in H2 (*Contact vector fields and
contact Hamiltonians*), D (*Contact Darboux theorem*), G4 (*Gray
stability*) and L2 (*Legendrian neighbourhood theorem*).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §3.5: (3.5.2) and (3.5.3) on p. 126, Example 3.5.6, p. 132, Lemma 3.5.14,
  Exercises 3.5.19(i), 3.5.20, 3.5.21 and 3.5.22(i).
* [D. McDuff, D. Salamon, *Errata for Introduction to Symplectic Topology,
  Third Edition*][McDuffSalamon2019Errata].
* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in
  Advanced Mathematics 109, Cambridge University Press, 2008, §§1.1, 2.1–2.3
  and 2.5 (cited by Tau Ceti's contact files, whose proofs the new files
  adapt).
