# Liouville structures

The detailed design of part 21 of `DESIGN.md`, *Liouville structures*. It
fixes the files of the part, its definitions and their API, the Lean names and
statements of its main results, what it takes from Tau Ceti, Mathlib and the
other parts, and the building issues in the order they can be done. It answers
the three questions that `DESIGN.md` leaves to it (see *Decisions*).

The part proves three milestones of `atlas/symplectic-manifolds.md`:
*Contact-type hypersurfaces and Liouville collars*, *Stable Hamiltonian
structures and their neighbourhood model* and *Completion of a strong
filling*. The source is McDuff–Salamon [McDuffSalamon2017], §3.5: Definition
3.5.27, Proposition 3.5.31 and Definition 3.5.32 (pp. 141–143), Exercise
3.5.37 (p. 146), Definition 3.5.38 (p. 147) and the completion on p. 148.
The collar theorem that the collar of a filling rests on is Hirsch, *Differential Topology*, Chapter 4, Theorem 6.1, and Lee,
*Introduction to Smooth Manifolds*, 2nd ed., Theorem 9.25.

Paths of Tau Ceti files are relative to `.lake/packages/TauCeti/TauCeti/`,
and every Tau Ceti name below was checked at commit `e0e414c`, the version
pinned when this file was written; `lakefile.toml` pins Tau Ceti
`c9d170eed5a8` now.
Paths of new files are under `SymplecticGeometry/`. Names are written in
full; a new name without a namespace is in `SymplecticGeometry`.

## Signs

The milestones are in the book's signs: a Liouville field `Y` of `ω` has
$\mathcal L_Y\omega=\omega$, its primitive is $\lambda=-\iota_Y\omega$ with
$d\lambda=-\omega$, the contact form induced on a hypersurface
$i:Q\to W$ is $\alpha=i^*\lambda=-i^*(\iota_Y\omega)$, with
$d\alpha=-i^*\omega$, and the symplectization form is $-d(e^s\alpha)$. Tau
Ceti's Liouville API (`Geometry/Symplectic/Liouville/`) is written for the
opposite primitive $\beta=\iota_Z\omega$, with $d\beta=\omega$, and its
symplectization is `TauCeti.SmoothForm.symplectization β`, which is
$e^t\beta$ on `ℝ × M`. As *Manifolds, families and signs* in `DESIGN.md`
says, the statements use Tau Ceti's objects with $\beta=-\lambda$ and $Z=Y$,
and no new definition is made for the sign:

| The book | In the statements |
|---|---|
| $\lambda=-\iota_Y\omega$ | `-ω.interiorₗ ⟨Y, hY⟩`, where Tau Ceti's primitive is `ω.interiorₗ ⟨Y, hY⟩` |
| $\alpha=-i^*(\iota_Y\omega)$ | `-SmoothForm.mpullback i hi β` with `β = ω.interiorₗ ⟨Y, hY⟩` |
| $-d(e^s\alpha)$ on `ℝ × Q` | `mextDerivₗ _ 1 (SmoothForm.symplectization (-α))` |
| $e^s\alpha$ | `SmoothForm.symplectization α` |
| the pair $(\Omega,\lambda)$ of a stable Hamiltonian structure | `TauCeti.SmoothForm.IsStableHamiltonian λ Ω` (one-form first) |
| the contact pair $(-d\alpha,\alpha)$ | `IsStableHamiltonian α (-mextDerivₗ _ 1 α)` |

Here `hY : ContMDiff I I.tangent ∞ (T% Y)` is the smoothness of `Y`, and
`ω.interiorₗ ⟨Y, hY⟩` is Tau Ceti's bundled interior product
`TauCeti.SmoothTwoForm.interiorₗ` (`Geometry/Symplectic/Manifold/Flat.lean`),
applied to `Y` as a smooth section; its value is `RoughForm.interior Y ω.val`
by `coe_interiorₗ`. For a strong filling `h`, `hY` is
`h.isOutwardPointingField.contMDiff`. The part adds no interior product of its own.

## Decisions

`DESIGN.md` leaves three questions to this file.

- **The representation of a strong filling.** A strong filling is a compact
  manifold with boundary, as the book has it, and not a compact domain of a
  given boundaryless manifold, which would presuppose the manifold that the
  completion builds. Its model is Tau Ceti's half-space,
  `[ChartedSpace (EuclideanHalfSpace (n + 1)) W]
  [IsManifold (𝓡∂ (n + 1)) ∞ W] [CompactSpace W] [T2Space W]`, since Tau
  Ceti's boundary API is written for it: the boundary
  `(𝓡∂ (n + 1)).boundary W` is a boundaryless manifold over
  `EuclideanSpace ℝ (Fin n)` (`TauCeti.boundaryChartedSpace`,
  `TauCeti.isManifold_boundary`), its inclusion is a smooth embedding
  (`TauCeti.isSmoothEmbedding_subtypeVal_boundary`), outward vectors are
  `TauCeti.IsOutwardPointing` (`Geometry/Manifold/Boundary/Orientation.lean`,
  chart-independent by `Boundary/TransitionNormal.lean`), and smooth collars
  are `TauCeti.SmoothCollar` (`Boundary/Collar/Smooth.lean`). Write `∂W` for
  the boundary type. The filling data is a predicate on a symplectic form
  `ω`, an open set `U` and a vector field `Y`:

  ```lean
  structure IsStrongFilling (ω : SmoothTwoForm (𝓡∂ (n + 1)) W) (U : Set W)
      (Y : (x : W) → TangentSpace (𝓡∂ (n + 1)) x) : Prop where
    isSymplectic : ω.IsSymplectic
    isOpen : IsOpen U
    boundary_subset : (𝓡∂ (n + 1)).boundary W ⊆ U
    isOutwardPointingField : IsOutwardPointingField Y
    mlieDerivForm_eq : ∀ x ∈ U, mlieDerivForm Y ω.val x = ω.val x
  ```

  `Y` is a global smooth field that is Liouville on `U`. This loses nothing
  against a field given only on `U`: `IsStrongFilling.of_contMDiffOn` cuts
  such a field off by a smooth bump function that is `1` near `∂W`. A
  *Liouville domain* is the case `U = univ`; it gets no predicate of its
  own. The contact manifold that `W` fills is its own boundary, with the
  form `fillingContactForm ω ⟨Y, hY⟩`, $-\iota^*(\iota_Y\omega)$, and the
  coorientation of that form. The book's filling of a given $(M,\xi)$ is
  this one transported by a diffeomorphism $\partial W\cong M$ carrying the
  form to a positive multiple of a defining form of $\xi$; no milestone
  states anything about the identification, so the library defines none.
  Tau Ceti's `TauCeti.IsLiouvilleDomain` and `IsLiouvilleCompletion` are not
  used as the representation; the completion of a Liouville domain is shown
  to be one of the latter (`isLiouvilleCompletion_completion`).
- **The Liouville collar at a boundary.** Tau Ceti's flows
  (`TauCeti.flowOf`) and collars (`Liouville/Collar.lean`) need a
  boundaryless model, and its smooth collars come without an existence
  theorem. The part therefore proves a collar theorem driven by the given
  field: for a smooth field `Y` pointing outward along a compact boundary,
  there are `ε > 0` and a `TauCeti.SmoothCollar` whose normal lines, run at
  speed `ε`, are the integral curves of `Y` through the boundary points, for
  times in $(-\varepsilon,0]$ (`TauCeti.SmoothCollar.exists_eq_of_isOutwardPointing`,
  in `Geometry/Manifold/Boundary/Collar/Flow/`). The curves are Tau Ceti's
  forward flow of `-Y` along the whole boundary
  (`TauCeti.IsOutwardPointingField.exists_contMDiffOn_boundaryFlow`), run
  backward, and Tau Ceti's `TauCeti.isLocalDiffeomorphAt_flowOut_boundary`
  makes their flow-out a local diffeomorphism along the boundary. For a strong filling the
  collar formulas $\Phi^*\lambda=e^s\alpha$ and $\Phi^*\omega=-d(e^s\alpha)$
  then follow from Tau Ceti's on the interior (see `Filling.lean`).
- **The completion of a Liouville domain against `TauCeti.IsLiouvilleCompletion`.**
  The completion $\widehat W$ is a boundaryless manifold over
  `EuclideanSpace ℝ (Fin (n + 1))`, built for any strong filling. For a
  Liouville domain, the extended primitive $\widehat\lambda$ and field
  $\widehat Y$ make it a Tau Ceti completion of the image of `W`:
  `TauCeti.IsLiouvilleCompletion ω̂ (-λ̂) (range toCompletion)`, with Tau
  Ceti's primitive $-\widehat\lambda$. So Tau Ceti's results on completions
  (the cylindrical end chart, the radial coordinate of
  `Liouville/CylindricalEnd.lean`) apply to it.

Further choices:

- **Hypersurfaces.** A hypersurface is `i : TauCeti.SmoothEmbedding J I ∞ Q W`
  with `hdim : finrank ℝ E' + 1 = finrank ℝ E`, in a boundaryless,
  Hausdorff, second countable `W` (the relative Poincaré lemma needs the
  last two). The book's *properly embedded* (`IsClosed (range i)`) is not
  needed by any step and is dropped; Tau Ceti's collar of variable width
  needs only a topological embedding.
- **Liouville near a hypersurface.** "A Liouville field near `Q`" is an open
  `U ⊇ range i` and a field `Y`, smooth on `U`, with
  `∀ x ∈ U, mlieDerivForm Y ω.val x = ω.val x`; transversality is Tau Ceti's
  `TauCeti.IsTransverseAlong J Y i`. For a closed `ω` this is Tau Ceti's
  `IsContactType` with the primitive `RoughForm.interior Y ω.val` (the local form of
  `TauCeti.exists_isRestrictedContactType_iff`).
- **Collars as diffeomorphisms of open sets.** A collar of a hypersurface is
  a diffeomorphism `D ≃ₘ⟮𝓘(ℝ).prod J, I⟯ V` between `D : Opens (ℝ × Q)`
  containing `{0} × univ` and `V : Opens W` containing `range i`, with the
  forms restricted along `Subtype.val`, the form of Tau Ceti's
  `TauCeti.SmoothTwoForm.exists_diffeomorph_opens_of_eq_along`
  (`DESIGN.md`, *Neighbourhood germs*). For compact `Q`, `D` is
  `Ioo (-ε) ε ×ˢ univ`.
- **Strips.** For stable Hamiltonian structures, the strip
  $(-\varepsilon,\varepsilon)\times M$ is `symmStrip M ε : Opens (ℝ × M)`
  (`Topology/Sets/Strip.lean`, for any topological space `X` in place of
  `M`), the open set `Ioo (-ε) ε ×ˢ univ`, a manifold as an open subset; a
  form on the strip is a form on `↥(symmStrip M ε)`. The smoothness and
  differential of its slice maps `symmStripMk hr` are in
  `Geometry/Manifold/Strip.lean`. The model form is defined on all of
  `ℝ × M` and restricted.
- **Dimension and degenerate cases.** Nothing assumes a dimension beyond the
  ones the statements need: `hdim` for hypersurfaces,
  `finrank ℝ E = 2 * m + 1` only for the wedge criterion of stable
  Hamiltonian structures. An empty `Q`, `M` or `∂W` makes every statement
  hold trivially: a filling with empty boundary is a closed symplectic
  manifold, whose completion is `W` itself with an empty end.

## Files and declarations

| File | Contents | Issue |
|---|---|---|
| `Geometry/Symplectic/Liouville/ContactType.lean` | contact type through local Liouville fields; both directions in the book's signs | 1 |
| `Geometry/Manifold/VectorField/Pullback.lean` | pullbacks of vector fields along local diffeomorphisms, and restrictions of vector fields to open subsets: smoothness and relatedness | — |
| `Geometry/Manifold/MFDeriv/Opens.lean` | differentiability of the inclusion of an open subset (`mdifferentiableAt_subtypeVal`, `mdifferentiable_subtypeVal`), beside Tau Ceti's file of that path | — |
| `Geometry/Symplectic/Liouville/Collar.lean` | the Liouville collar of a hypersurface; first milestone | 2 |
| `Geometry/Contact/StableHamiltonian.lean` | wedge criterion, smooth Reeb field, invariance, contact case; the model and its converse; second milestone | 3, 4 |
| `Geometry/Contact/Symplectization/Basic.lean` | Tau Ceti's symplectization form written with `funSMulₗ`, beside Tau Ceti's file of that path | 4 |
| `Topology/Sets/Strip.lean` | the open strip `(-ε, ε) × X` of `ℝ × X` and the tube lemma for it | 4 |
| `Geometry/Manifold/Strip.lean` | the slice maps of the strip as smooth maps, their differential, and slices of two-forms | 4 |
| `Geometry/Manifold/SmoothEmbedding/Basic.lean` | the right slice `x ↦ (c, x)` of a product as a smooth embedding, beside Tau Ceti's file of that path | 4 |
| `Geometry/Manifold/Boundary/Charts.lean` | boundary points in the extended charts of the half-space model; outward vectors are not tangent to the boundary | 5 |
| `Geometry/Manifold/Boundary/Collar/Flow/Local.lean` | integral curves of an outward field are in the interior at times from which they run forward | 5 |
| `Geometry/Manifold/Boundary/Collar/Flow/Basic.lean` | the collar of a compact boundary along an outward field | 6 |
| `Topology/Compactness/SigmaCompact.lean` | σ-compact open neighbourhoods of a compact set in a locally compact space (`IsCompact.exists_isOpen_isSigmaCompact_subset`); used in `Flow/Basic.lean` | — |
| `Geometry/Manifold/Boundary/Collar/Opens.lean` | the diffeomorphism `∂V ≃ ∂W` for an open `V ⊇ ∂W` (`SymplecticGeometry.diffeomorphBoundaryOpens`), and a collar of `∂V` as one of `∂W` (`TauCeti.SmoothCollar.ofOpens`); used in `Flow/Basic.lean` | — |
| `Geometry/Symplectic/Liouville/Filling.lean` | `IsStrongFilling`, its contact form, its Liouville collar | 7 |
| `Geometry/Symplectic/Liouville/Scaling.lean` | Liouville scaling along integral curves, on a boundaryless manifold and in the interior of a manifold with boundary, for the collar of `Filling.lean` | 7 |
| `Geometry/Manifold/DifferentialForm/Continuity.lean` | continuity in the parameter of the pullbacks of a form along the slices of a `C¹` map on a product, for the collar of `Filling.lean`, beside Tau Ceti's file of that path | 7 |
| `Geometry/Manifold/Boundary/Collar/Local.lean` | smoothness of Tau Ceti's normal ray of the half-line on `[0, ∞)`, and the ray on `(-∞, 1)` as a depth map into `normalIioOpens 1`, for the collars of `Flow/Basic.lean` and `Filling.lean` and the end of `End.lean`, beside Tau Ceti's file of that path | 7 |
| `Geometry/Manifold/Boundary/Interior.lean` | maps into Tau Ceti's charted interior `I.interior M` (`ContMDiff.codRestrict_interior`), its identification with the open interior (`ModelWithCorners.interiorOpensDiffeomorph`) and the orientation carried across it (`TauCeti.Manifold.Orientation.toInterior`); used in `End.lean` and `Collar/Interior.lean` | — |
| `Geometry/Manifold/ModelTransport/Remodel.lean` | a manifold re-modelled along a diffeomorphism of model spaces (`SymplecticGeometry.Remodel`), and its diffeomorphism with the manifold; used in `End.lean` and `Gluing/CapDiscs/Basic.lean` | — |
| `Geometry/Manifold/Boundary/Collar/Interior.lean` | interior collar points, and the collar coordinates on the part of the interior covered by the collar (`SmoothCollar.interiorCoord`); used in `End.lean` and `Gluing/CapDiscs/Basic.lean` | — |
| `Geometry/Manifold/Boundary/Collar/End.lean` | attaching the end `[0, ∞) × ∂W` along a smooth collar | 8 |
| `Geometry/Manifold/VectorField/Prod.lean` | the value `(v, 0)` of the product of a constant field and the zero field (`TauCeti.Manifold.prodVectorField_constVectorField_zero_apply`); used in `Completion.lean` and `Domain.lean`, beside Tau Ceti's file of that path | — |
| `Geometry/Symplectic/Liouville/Completion.lean` | $\widehat\omega$, $\widehat Y$, $\widehat\lambda$; third milestone | 9, 10 |
| `Geometry/Symplectic/Liouville/Domain.lean` | the completion of a Liouville domain is a Tau Ceti completion | 11 |

`ContactType.lean`, `Collar.lean`, `Scaling.lean`, `StableHamiltonian.lean`,
`Completion.lean` and `Domain.lean` have the paths of Tau Ceti files and
extend them. No folder below has the name of a Tau Ceti file at its place:
Tau Ceti's `Geometry/Manifold/Boundary/Collar/` is a folder with no
`Flow.lean` or `End.lean`, and because Tau Ceti has
`Geometry/Contact/StableHamiltonian.lean` and
`Geometry/Symplectic/Liouville/Completion.lean`, these stay single files
(each under 1000 lines) instead of becoming folders.

### `Geometry/Symplectic/Liouville/ContactType.lean`

In `TauCeti`, beside Tau Ceti's file, for `ω` a closed `C¹` two-form
(`IsSmoothForm I 1`, a rough form):

- `isContactType_interior`: for `U`, `Y` as in the next item, `ι` is of
  contact type with the primitive `RoughForm.interior Y ω.val`; the reverse
  direction of the next item.
- `exists_isContactType_iff`: `(∃ β, IsContactType J ω.val β ι)` if and only
  if there are an open `U ⊇ range ι` and a field `Y`, smooth on `U`, with
  `∀ x ∈ U, mlieDerivForm Y ω.val x = ω.val x` and
  `IsTransverseAlong J Y ι`; then `β` may be taken `RoughForm.interior Y ω.val`.
  The local version of `exists_isRestrictedContactType_iff`, by the
  pointwise Cartan formula `mlieDerivForm_eq_mextDeriv_interior_apply` at
  each point of `U` and `mextDeriv_congr_of_eventuallyEq`, with no passage
  to the open submanifold `U`.
- `SmoothEmbedding.exists_isContactForm_eq_neg_mpullback_interior` (the book's
  direction 2 ⇒ 1): for `ω` symplectic, `hdim`, and `U`, `Y` as above, there
  is `α : SmoothForm J Q ℝ 1` with value
  `-mpullback J I i (RoughForm.interior Y ω.val)`, a contact form with
  `mextDerivₗ J 1 α = -SmoothForm.mpullback i _ ω`. From the pointwise
  `isContactFormAt_mpullback` (`IsContactType.isContactForm_mpullback` needs
  a primitive smooth on all of `W`) and `SmoothForm.isContactForm_neg_iff`;
  the derivative by naturality of `d` (`mpullback_mextDeriv_at`) and
  `isContactType_interior`. (If the
  global form `ω.interiorₗ ⟨Y, hY⟩` is needed, `Y` is first cut off to a global
  field equal to it near `range i`, as in `IsStrongFilling.of_contMDiffOn`.)
- `SmoothEmbedding.exists_liouville_of_isContactForm` (the converse, for a
  prescribed form): for `ω` symplectic and a contact form
  `α : SmoothForm J Q ℝ 1` with `mextDerivₗ J 1 α = -i^*ω` (no `hdim`: the
  proof does not use it), there are an
  open `U ⊇ range i` and a field `Y`, smooth on `U` and Liouville there,
  transverse along `i`, with `-mpullback J I i (RoughForm.interior Y ω.val) = α.val`.
  Route: the smooth retraction `π : T → Q` of an open `T ⊇ range i`
  (`SmoothEmbedding.exists_contMDiffOn_retraction`); $\bar\alpha=\pi^*\alpha$; the relative
  Poincaré lemma `SmoothEmbedding.exists_isSmoothForm_relative_primitive`
  for the closed form $\omega+d\bar\alpha$ on `T`, whose pullback by `i`
  vanishes, gives $\eta$ with $d\eta=\omega+d\bar\alpha$, vanishing along
  `i`; $\lambda=\bar\alpha-\eta$ has $d\lambda=-\omega$ and $i^*\lambda=\alpha$
  (these steps, for forms of any degree, are
  `SmoothEmbedding.exists_mextDeriv_eq_and_mpullback_eq`, which issue 1 adds
  to `Geometry/Manifold/TubularNeighborhood/RelativePoincare.lean` of
  *Moser isotopy*);
  `Y` is the field with $\iota_Y\omega=-\lambda$, given at each point by the
  inverse flat map `(ω.flat x).inverse`
  (`SmoothTwoForm.IsNondegenerate.interior_flat_inverse_ofSubsingleton`, in
  `Geometry/Symplectic/Manifold/Flat.lean` of *Moser isotopy*, and Tau Ceti's
  `SmoothTwoForm.contMDiffAt_inverse_flat` for smoothness on `U`); it is Liouville by
  Cartan's formula. Transversality: at a point where `Y` is tangent,
  $Y=di(v)$ with $\alpha(v)=0$ and $\iota_v d\alpha=\alpha$, so `v` lies in
  the kernel of $d\alpha$ on $\ker\alpha$, hence `v = 0`, while
  $\alpha\neq 0$ there.

Expected size: 400 lines.

### `Geometry/Symplectic/Liouville/Collar.lean`

In `TauCeti`, beside Tau Ceti's file, for `ω` symplectic, `hdim`, `U` and `Y`
as above with `Y` Liouville on `U` and transverse along `i`, and `α` with
`hα : α.val = -mpullback J I i (RoughForm.interior Y ω.val)` (a hypothesis,
since `Y` is smooth only on `U`):

- `IsLiouvilleCollar ω Y i α Φ φ`, in `SymplecticGeometry`, a `Prop`-valued
  structure, for
  `Φ : D ≃ₘ⟮𝓘(ℝ).prod J, I⟯ V` with `D : Opens (ℝ × Q)`, `V : Opens W`, and
  `φ : ℝ × Q → W`: its fields are `zero_mem : ∀ q, (0, q) ∈ D`,
  `mem_of_mem : ∀ p ∈ D, ∀ s ∈ uIcc 0 p.1, (s, p.2) ∈ D`,
  `coe_apply : Φ p = φ p`, `apply_zero : φ (0, q) = i q`,
  `isMIntegralCurveOn` (each `t ↦ φ (t, q)` an integral curve of `Y` on the
  slice of `D`), `mpullback_eq`:
  `mpullback _ I Φ ω.val = (mextDerivₗ _ 1 (SmoothForm.symplectization (-α))).val|D`,
  that is $\Phi^*\omega=-d(e^s\alpha)$, and `mpullback_interior_eq`:
  `mpullback _ I Φ (RoughForm.interior Y ω.val) = (symplectization (-α)).val|D`,
  that is $\Phi^*\lambda=e^s\alpha$; both are pullbacks of rough forms to `D`.
  `range_subset : range i ⊆ V` is a theorem.
- `SmoothEmbedding.exists_liouvilleCollar`: there are `D : Opens (ℝ × Q)`,
  `V : Opens W` with `V ⊆ U`,
  `Φ : D ≃ₘ⟮𝓘(ℝ).prod J, I⟯ V` and `φ : ℝ × Q → W` with
  `IsLiouvilleCollar ω Y i α Φ φ`.
  From Tau
  Ceti's `exists_continuous_pos_injOn_flowOf_comp` (variable width, `D` the
  set `|t| < ε q`) applied on the open submanifold `U` with
  $\beta=\iota_Y\omega$, and its formulas
  `mpullback_flowOf_comp_apply_eq_symplectization` and
  `mpullback_flowOf_comp_mextDeriv_apply`. Second
  countability and Hausdorffness give the pseudometrizability that the
  variable width needs.
- `SmoothEmbedding.exists_liouvilleCollar_of_compactSpace`: for compact `Q`,
  the same with `D = symmStrip Q ε` for some `ε > 0`, from the collar of
  variable width and `exists_symmStrip_le`.
- The milestone, in two theorems: for `ω` symplectic and `hdim`,
  `SmoothEmbedding.exists_isContactForm_iff_exists_liouville`: (1) some
  contact `α` on `Q` has
  `mextDerivₗ J 1 α = -i^*ω` if and only if (2) some field, Liouville and
  smooth on an open `U ⊇ range i`, is transverse along `i`; and
  `SmoothEmbedding.exists_liouvilleCollar_of_isContactForm`: for every
  such `α` there are `U` and `Y` as in
  `exists_liouville_of_isContactForm` together with a collar as in
  `exists_liouvilleCollar`, and with `D = symmStrip Q ε` when `Q` is
  compact. Docstring line of both: "Milestone: *Contact-type hypersurfaces and
  Liouville collars*."

The book's Proposition 3.5.31 assumes `Q` compact; the statement here holds
without it, as the page also states, so no `ERRATA.md` entry is needed.

Expected size: 300 lines.

### `Geometry/Contact/StableHamiltonian.lean`

In `TauCeti.SmoothForm`, beside Tau Ceti's file, for `α` a one-form and `ω`
a two-form on `M` (the book's $(\Omega,\lambda)$ is `IsStableHamiltonian α ω`
with `α = λ`, `ω = Ω`). It imports
`Geometry/Manifold/DifferentialForm/Smooth.lean` of *Moser isotopy* for
`SmoothForm.bilinFormAt_smul`, `_neg`, `SmoothForm.mpullback_funSMulₗ`,
`funSMulₗ_const`, `funSMulₗ_add` and `funSMulₗ_one`, and
`Geometry/Contact/Symplectization/Basic.lean` for
`symplectization_eq_funSMulₗ`. It imports
`Geometry/Manifold/DifferentialForm/Flow/Family.lean` of *Contact geometry*
for `SmoothForm.timeInterior` and `SmoothForm.mextDerivₗ_timeInterior`. Issue 3:

- `isStableHamiltonian_iff_wedge_wedgePow_apply_ne_zero`: for
  `finrank ℝ E = 2 * m + 1`, `IsStableHamiltonian α ω` if and only if `ω` is
  closed, `(wedge α (ω.wedgePow m)).val x ≠ 0` for every `x`, and the kernel
  condition holds. The book's $\lambda\wedge\Omega^{n-1}\neq0$ in dimension
  $2n-1$. From `ContinuousAlternatingMap.pairedWedge_wedgePow_ne_zero_iff`
  (`Geometry/Contact/Volume.lean`), which is stated for any two-form; the
  pointwise step is that of `isContactFormAt_iff_wedge_wedgePow_apply_ne_zero`.
- `contMDiff_characteristicVectorField`: if `α_x` is contact for `ω_x` at
  every `x`, the characteristic field is smooth. Adapts the proof of
  `IsContactForm.contMDiff_reebVectorField` (`Geometry/Contact/Flat.lean`,
  through `contactFlatEquiv`) with `ω` in place of `dα`: the bundle map
  $v\mapsto\iota_v\omega+\alpha(v)\alpha$ is invertible by
  `Module.Dual.isContact_iff_separatingLeft_add_smulRight`, and $R$ is the
  preimage of $\alpha$. The module docstring credits the adapted proof.
- `IsStableHamiltonian.mlieDerivForm_characteristicVectorField_twoForm` and
  `..._oneForm`: $\mathcal L_R\omega=0$ and $\mathcal L_R\alpha=0$, by
  Cartan's formula with `interior_characteristicVectorField`,
  `apply_characteristicVectorField` and
  `IsStableHamiltonian.interior_mextDeriv_characteristicVectorField`.
- `IsStableHamiltonian.mpullback_flowOf_characteristicVectorField_twoForm`
  and `..._oneForm`: the flow of `R` pulls `ω` and `α` back to themselves
  where it is defined, from Tau Ceti's
  `mpullback_flowOf_apply_of_mextDeriv_interior_eq_zero` and
  `mpullback_flowOf_apply_of_interior_mextDeriv_eq_zero`
  (`Geometry/Manifold/DifferentialForm/Flow.lean`); on a compact
  boundaryless `M` the field is complete and the global flow is meant.
- `IsContactForm.isStableHamiltonian_neg`: for a contact form `α`,
  `IsStableHamiltonian α (-mextDerivₗ I 1 α)`, and
  `characteristicVectorField_neg_mextDerivₗ` (for every one-form, so without
  the contact hypothesis): its characteristic field is `α.reebVectorField`,
  since negating the two-form changes neither its kernel nor the
  normalization `α(R) = 1`. From
  `IsContactForm.isStableHamiltonian` and the invariance of the pointwise
  contact condition and of kernels under negating the two-form.

Issue 4, in `TauCeti.SmoothForm`:

- `stableHamiltonianModel α σ : SmoothTwoForm (𝓘(ℝ).prod I) (ℝ × M)`,
  $\Omega-d(r\lambda)$, defined as
  `SmoothForm.mpullback Prod.snd _ σ - mextDerivₗ _ 1 (r • SmoothForm.mpullback Prod.snd _ α)`
  with `r` the first coordinate. API: `stableHamiltonianModel_def`,
  `stableHamiltonianModel_apply` (the value
  $\Omega-r\,d\lambda-dr\wedge\lambda$ on tangent vectors of `ℝ × M`),
  `mpullback_prodMk_stableHamiltonianModel` (the slice at `r` is
  $\Omega-r\,d\lambda$), `isClosed_stableHamiltonianModel` (for closed `σ`),
  and `SymplecticGeometry.symmStrip M ε : Opens (ℝ × M)` with
  `SymplecticGeometry.mem_symmStrip_iff`.
- `IsStableHamiltonian.nondegenerate_bilinFormAt_stableHamiltonianModel_zero`: at
  `(0, x)` the model is nondegenerate, by the pointwise contact condition
  (`Module.Dual.isContact_iff_nondegenerate_symplectizationForm`, or the
  splitting `isCompl_kerDistribution_span_characteristicVectorField`).
- `IsStableHamiltonian.exists_isSymplectic_stableHamiltonianModel` (compact
  `M`): some `ε > 0` makes the model symplectic on `symmStrip M ε`; nondegeneracy
  is open and the tube lemma gives a uniform `ε`.
- `IsStableHamiltonian.ker_mpullback_prodMk_stableHamiltonianModel`: where
  the model is nondegenerate along the slice `{r} × M`, the kernel of the
  slice form at `x` is the kernel of `ω_x`: it contains it by the kernel
  condition, and has dimension one because a nondegenerate form restricts
  to a form of corank at most one on a hyperplane.
- `stableHamiltonianModel_neg_mextDerivₗ`: for a one-form `α`,
  `stableHamiltonianModel α (-mextDerivₗ I 1 α)` is `-mextDerivₗ` of
  $(1+r)\alpha$; and
  `mpullback_subtypeVal_stableHamiltonianModel_neg_mextDerivₗ`: on an open
  `U` where `r > -1`, it is the pullback of
  `mextDerivₗ _ 1 (SmoothForm.symplectization (-α))` along
  $(r,x)\mapsto(\log(1+r),x)$.
- `exists_mpullback_eq_stableHamiltonianModel` (the converse; compact
  boundaryless Hausdorff second countable `M`): let `σ` be a symplectic form
  on `symmStrip M ε` whose slices $\sigma_r$ (pullbacks along `x ↦ (r, x)`) have
  kernels independent of `r`. Put $\Omega_0=\sigma_0$ and
  $\lambda_0=-$ the slice at `0` of $\iota_{\partial_r}\sigma$. Then
  `IsStableHamiltonian λ₀ Ω₀`, and for some `δ ∈ (0, ε]` there is a map
  `Φ : symmStrip M δ → symmStrip M ε`, injective and a local diffeomorphism, with
  `Φ (0, x) = (0, x)` and `Φ^*σ` the model of $(\Omega_0,\lambda_0)$
  restricted to `symmStrip M δ`. Route: as `σ` is closed, each slice $\Omega_r$
  is closed and its derivative in `r` is $-d_M\lambda_r$; since `σ` is
  nondegenerate, $\lambda_r$ does not vanish on the kernel line shared by
  all slices; taking the `r`-derivative of $\iota_Z\Omega_r=0$, for `Z` a
  local section of that line, shows $\iota_Z d\lambda_0=0$. Along the zero
  slice, `σ` and the model coincide on the whole tangent space
  $T_{(0,x)}(\mathbb R\times M)$, so Tau
  Ceti's compact relative Moser theorem
  `SmoothTwoForm.exists_diffeomorph_opens_of_eq_along` along
  `x ↦ (0, x)` gives a diffeomorphism of neighbourhoods, and the tube
  lemma a strip inside. On the strip, the slice at `r` is the pullback along
  `SymplecticGeometry.symmStripMk hr : M → symmStrip M ε`, and
  `λ₀` is `zeroSliceOneForm hε σ`. The first half is
  `isStableHamiltonian_zeroSliceOneForm` and
  `val_symmStripMk_zero_eq_stableHamiltonianModel`.
- The milestone,
  `IsStableHamiltonian.characteristicVectorField_and_stableHamiltonianModel`:
  for compact boundaryless `M` with `finrank ℝ E = 2 * m + 1`: the wedge
  criterion; uniqueness of `R` (Tau Ceti's `eq_characteristicVectorField_iff`);
  invariance of both forms under its flow; the model symplectic on some
  strip with slice kernels `ker ω`; the contact case; and the converse
  above, as a conjunction. Docstring line: "Milestone: *Stable Hamiltonian
  structures and their neighbourhood model*."

Expected size: 300 lines for issue 3, 500 for issue 4.

### `Geometry/Manifold/Boundary/Collar/Flow/Local.lean`

For `W` as in *Decisions* (no compactness) and a field `Y` pointing outward
along the boundary, the backward curves of `Y` from the boundary are Tau
Ceti's (see `Flow/Basic.lean`). This file adds:

- `IsMIntegralCurveOn.mem_interior_of_isOutwardPointing`: an integral curve
  of `Y` on `s` is in the interior of `W` at each time `t` with
  `s ∈ 𝓝[≥] t`, since a curve running forward from a boundary point has no
  outward velocity there (Tau Ceti's
  `TauCeti.not_isOutwardPointing_curveVelocityWithin_Ici`).

Expected size: 500 lines.

### `Geometry/Manifold/Boundary/Collar/Flow/Basic.lean`

In `TauCeti.SmoothCollar`, for `W` with `[CompactSpace ↥((𝓡∂ (n + 1)).boundary W)]`
and a field `Y` with `hY : IsOutwardPointingField Y`:

- `exists_eq_of_isOutwardPointing`: there are `ε > 0`, a map
  `Φ : ℝ × ∂W → W` with `Φ (0, x) = x` and each `s ↦ Φ (s, x)` an integral
  curve of `Y` on `Ioc (-ε) 0`, and `c : SmoothCollar n ∞ W` with
  `c (x, t) = Φ (-ε * (t : EuclideanHalfSpace 1).val 0, x)`. `Φ (s, x)` is
  Tau Ceti's forward flow of `-Y` from the boundary
  (`TauCeti.IsOutwardPointingField.exists_contMDiffOn_boundaryFlow`) at
  time `-s`; compactness of `∂W` gives a uniform time; Tau Ceti's
  `TauCeti.isLocalDiffeomorphAt_flowOut_boundary` makes the flow-out a local
  diffeomorphism at each `(x, 0)`; injectivity on a thinner
  collar comes from injectivity on `{0} × ∂W` and these local
  diffeomorphisms, as in Tau Ceti's `exists_pos_injOn_flowOf_comp`
  (`Set.InjOn.exists_isOpen_superset_isLocalDiffeomorphOn` and the tube
  lemma), whose proof this adapts and credits.
- `exists_eq_of_isOutwardPointing_of_subset`: the same with `range c` inside
  a given open `U ⊇ ∂W`.

This is a smooth collar theorem for manifolds with an outward field; such a
field exists on a σ-compact manifold (Tau Ceti's `exists_isOutwardPointingField`),
so with it this gives smooth collars of compact boundaries, which Tau Ceti lacks.
The same file states that corollary, for every Hausdorff `W` with compact
boundary: `exists_range_subset` (a smooth collar with `range c` inside a given
open `U ⊇ ∂W`) and the instance `instNonempty : Nonempty (SmoothCollar n ∞ W)`.
It collars a σ-compact open `V ⊇ ∂W` inside `U`, from
`Topology/Compactness/SigmaCompact.lean`, which it imports, and carries the
collar to `W` through `Boundary/Collar/Opens.lean`.

Expected size: 400 lines.

### `Geometry/Symplectic/Liouville/Filling.lean`

For `W` as in *Decisions*:

- `IsStrongFilling` (above), with `isStrongFilling_iff`,
  `IsStrongFilling.mono` (shrinking `U` to an open set that still contains
  `∂W`), `IsStrongFilling.of_contMDiffOn` (from a field smooth only on `U`,
  by a bump function from
  `IsClosed.exists_contMDiffMap_tsupport_subset_eventually_eq_one`, with `∂W` closed by
  Mathlib's `ModelWithCorners.isClosed_boundary`), and
  `IsStrongFilling.isContactType`: the boundary inclusion is of contact type
  for `ω` with primitive `ω.interiorₗ ⟨Y, hY⟩`, as Tau Ceti's `IsContactType` (it
  takes any model; transversality from outwardness).
- `fillingContactForm ω ⟨Y, hY⟩ : SmoothForm (𝓡 n) ∂W ℝ 1`, the form
  $-\iota^*(\iota_Y\omega)$ along the boundary inclusion, defined for any
  smooth section `⟨Y, hY⟩` (so that it needs no junk value), with
  `fillingContactForm_def` and
  `IsStrongFilling.isContactForm_fillingContactForm` and
  `IsStrongFilling.mextDerivₗ_fillingContactForm`, $d\alpha=-\iota^*\omega$,
  both from
  `TauCeti.SmoothEmbedding.exists_isContactForm_eq_neg_mpullback_interior`
  (`Liouville/ContactType.lean`), applied to the boundary inclusion.
- `IsStrongFilling.exists_liouvilleCollar`: there are `ε > 0`,
  `Φ : ℝ × ∂W → W` and `c : SmoothCollar n ∞ W` as in
  `SmoothCollar.exists_eq_of_isOutwardPointing`, with `range c ⊆ U`, such
  that on `Ioo (-ε) 0 ×ˢ univ`,
  `mpullback Φ (-(ω.interiorₗ ⟨Y, hY⟩)) = symplectization (fillingContactForm ω ⟨Y, hY⟩)`
  and `mpullback Φ ω = mextDerivₗ _ 1 (symplectization (-fillingContactForm ω ⟨Y, hY⟩))`,
  $\Phi^*\lambda=e^s\alpha$ and $\Phi^*\omega=-d(e^s\alpha)$. Route: on the
  interior, re-modelled over `EuclideanSpace ℝ (Fin (n + 1))` by Tau Ceti's
  `TauCeti.BoundarylessModel` (`Geometry/Manifold/ModelTransport/`), with
  `BoundarylessManifold` from the library's
  `Geometry/Manifold/IsManifold/InteriorBoundary.lean`, Tau Ceti's
  `mpullback_flowOf_comp_apply_eq_symplectization` applies to the pushed-in
  copy `Φ (-δ, ·)` of the boundary; letting `δ → 0` with the smoothness of
  `c` up to the boundary identifies the restricted form with `-α`. (A
  direct alternative: $\frac{d}{ds}\Phi_s^*\beta=\Phi_s^*\mathcal L_Y\beta=\Phi_s^*\beta$
  and $\beta(Y)=0$.)

Expected size: 400 lines.

### `Geometry/Manifold/Boundary/Collar/End.lean`

In `TauCeti.SmoothCollar`, for a smooth `W` modelled on `𝓡∂ (n + 1)`
(`IsManifold (𝓡∂ (n + 1)) ∞ W`, which the gluing diffeomorphism needs) and
`c : SmoothCollar n ∞ W`; Hausdorffness of `W` is assumed only for the `T2Space`
instance and `isClosedEmbedding_inclusion`. This is differential topology, with no forms:

- `WithEnd c : Type`, the manifold $W\cup_{\partial W}([0,\infty)\times\partial W)$,
  the space `SymplecticGeometry.GluedAlong` (`Gluing/Pair.lean`) of a diffeomorphism of
  open subsets of the interior
  of `W` (as Tau Ceti's charted interior `(𝓡∂ (n + 1)).interior W`,
  `TauCeti/Geometry/Manifold/Boundary/Interior.lean`) and
  `Ioi (-1) × ∂W`, `(s, x) ↦ c (x, -s)` on `Ioo (-1) 0 × ∂W`; the second piece is
  re-modelled by a linear equivalence
  `ℝ × EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1))`
  as `SymplecticGeometry.Remodel` (`ModelTransport/Remodel.lean`). The pieces,
  overlaps and the gluing diffeomorphism are private, except the interior overlap and its
  collar coordinates, `c.interiorRange` and `c.interiorCoord` of
  `Boundary/Collar/Interior.lean`. Instances, from `GluedAlong`: `TopologicalSpace`
  (`c.topologicalSpaceWithEnd`), `T2Space` (for `T2Space W`),
  `ChartedSpace (EuclideanSpace ℝ (Fin (n + 1)))` (`c.chartedSpaceWithEnd`),
  `IsManifold (𝓡 (n + 1)) ∞`, with no compactness or countability
  hypothesis.
- `WithEnd.inclusion : W → c.WithEnd`, with `isSmoothEmbedding_inclusion`
  (Mathlib's `IsSmoothEmbedding (𝓡∂ (n + 1)) (𝓡 (n + 1)) ∞`) and
  `isClosedEmbedding_inclusion`, `isOpenEmbedding_inclusion_comp_subtypeVal`
  and `isLocalDiffeomorphAt_inclusion` on the interior; smoothness at the
  boundary through the inverse of `c` (`SmoothCollar.diffeomorphOpensRange`).
  `WithEnd.retraction : C(c.WithEnd, W)` is a left inverse
  (`retraction_inclusion`, `retraction_endMap`).
- `WithEnd.endMap : ℝ × ∂W → c.WithEnd`, with `contMDiffOn_endMap`,
  `injOn_endMap` and `isLocalDiffeomorphOn_endMap` on `Ioi (-1) ×ˢ univ`
  (values for `s ≤ -1` are junk), `endMap_neg_eq_inclusion`
  (`endMap (-t, x) = inclusion (c (x, t))` for `t ∈ [0, 1)`) and
  `endMap_zero`.
- `WithEnd.range_inclusion_union`: `range inclusion ∪ endMap '' (Ioi 0 ×ˢ univ)`
  is everything, and `WithEnd.disjoint_range_inclusion_endMap_image`: the two
  are disjoint; `WithEnd.isOpen_endMap_image`;
  `WithEnd.exists_eq_inclusion_or_endMap` for case analysis; and
  `WithEnd.isOpenCover` (of `![interiorPart c, endPart c]`, the images of the
  interior of `W` and of `Ioi (-1) ×ˢ univ`), the form in which forms and
  fields are glued.

Expected size: 600 lines.

### `Geometry/Symplectic/Liouville/Completion.lean`

For `h : IsStrongFilling ω U Y`, with the collar `c`, `ε` and `Φ` of
`h.exists_liouvilleCollar` chosen once (`Classical.choose`, as `h.collarWidth`,
`h.collarFlow` and `h.collar`) and `α := fillingContactForm ω ⟨Y, hY⟩`.
Issue 9:

- `IsStrongFilling.Completion h := c.WithEnd`, with the instances above,
  `h.toCompletion : W → h.Completion := WithEnd.inclusion`, and
  `h.completionEnd : ℝ × ∂W → h.Completion`, `(s, x) ↦ endMap (s / ε, x)`,
  so that `s` is the Liouville time; `completionEnd_zero`
  (`completionEnd (0, x) = toCompletion x`) and
  `completionEnd_eq_toCompletion` (for `s ∈ (-ε, 0]`,
  `completionEnd (s, x) = toCompletion (Φ (s, x))`).
- `h.completionForm : SmoothTwoForm (𝓡 (n + 1)) h.Completion`, equal to the
  transport of `ω` on the image of the interior, and on the end piece to
  the symplectization form $-d(e^s\alpha)$; it is defined pointwise, through
  the inverse differential of the end map on the image of
  `Ioi (-ε) ×ˢ univ` and of the inclusion elsewhere, the pieces
  agreeing on the overlap by `h.exists_liouvilleCollar`; smoothness by
  `IsLocalDiffeomorphAt.contMDiffAt_mpullback_form_iff`.
  Likewise `h.completionPrimitive` (λ on `W`, $e^s\alpha$ on the end) and
  the vector field `h.completionField` (`Y` on `W`, $\partial_s$ on the
  end; the pieces agree because the collar lines are integral curves of
  `Y`), with smoothness lemmas.
- The characterizing lemmas: `mpullback_toCompletion_completionForm`
  (`= ω`), `mpullback_completionEnd_completionForm` (on `Ioi (-ε) ×ˢ univ`,
  `= mextDerivₗ _ 1 (symplectization (-α))`), the same two for
  `completionPrimitive` (`= -(ω.interiorₗ ⟨Y, hY⟩)` and `= symplectization α`),
  and `mfderiv_toCompletion_apply` (`d toCompletion (Y x) = completionField (toCompletion x)`)
  and `mfderiv_completionEnd_apply` (∂_s goes to `completionField`).

Issue 10:

- `IsStrongFilling.isSymplectic_completionForm`: closed and nondegenerate,
  checked on the two pieces (on the end by Tau Ceti's
  `IsContactForm.isSymplectic_mextDerivₗ_symplectization` with
  `isContactForm_neg_iff`).
- `IsStrongFilling.mlieDerivForm_completionField_of_mem`: Liouville
  at every point of `toCompletion '' U ∪ completionEnd '' (Ioi 0 ×ˢ univ)`;
  on the end from `SmoothForm.isLiouvilleVectorField_symplectization`.
- `interior_completionField_completionForm`
  ($\iota_{\widehat Y}\widehat\omega=-\widehat\lambda$), for every strong filling.
- For a Liouville domain (`U = univ`):
  `mextDerivₗ_completionPrimitive`
  (`mextDerivₗ _ 1 h.completionPrimitive = -h.completionForm`) and
  `isLiouvilleVectorField_completionField`.
- The milestone, `IsStrongFilling.isSymplectic_completionForm_and_extends`:
  the conjunction of `isSymplectic_completionForm`, the two pullback
  formulas for `completionForm` (on `W` and on `Ici 0 ×ˢ univ` of the end),
  the decomposition `range toCompletion ∪ completionEnd '' (Ioi 0 ×ˢ univ) = univ`
  with the two disjoint, the collar statement of `h.exists_liouvilleCollar`
  (in the form $\omega=-d(e^s\alpha)$ on $(-\varepsilon,0)\times\partial W$,
  and at `s = 0` through `completionEnd_eq_toCompletion` on `Ioc (-ε) 0`),
  the Liouville property of `completionField` on the end with
  `mfderiv_completionEnd_apply`, the field identity, and, when `U = univ`,
  the pullback formulas of `completionPrimitive` and its derivative.
  Docstring line: "Milestone: *Completion of a strong filling*."

Expected size: 450 lines for issue 9, 350 for issue 10.

### `Geometry/Symplectic/Liouville/Domain.lean`

In `SymplecticGeometry.IsStrongFilling`, beside Tau Ceti's file:

- `isLiouvilleCompletion_completion [CompactSpace W] (h : IsStrongFilling ω univ Y)`:
  `TauCeti.IsLiouvilleCompletion h.completionForm (-h.completionPrimitive)
  (range h.toCompletion)`. The domain conditions: nondegeneracy and
  $d(-\widehat\lambda)=\widehat\omega$ from issue 10; compactness and
  `range ⊆ interior` (a boundaryless model); the field
  `completionField`, with $\iota\widehat\omega=-\widehat\lambda$; the
  function `f` equal to `max s (-ε / 2)` on the end piece and `-ε / 2` on the
  rest of the image of `W`, continuous, with `range toCompletion = {f ≤ 0}`
  and $df(\widehat Y)=1$ along `f = 0`. Completeness of `completionField`:
  on the end it is $\partial_s$; backward lines from `W` stay in the
  compact image of `W`, as the field points outward along its boundary;
  every point flows into `W` in some time.

Expected size: 300 lines.

## What the part uses

- *Smooth families*: `Geometry/Manifold/LocalDiffeomorph/Basic.lean`, in
  `Collar/Flow/Local.lean` and `Collar/Flow/Basic.lean`
  (`SymplecticGeometry.isLocalDiffeomorph_id`).
- *Smooth families*: `Geometry/Manifold/LocalDiffeomorph/OpenSubset.lean`
  (`IsLocalDiffeomorphAt.subtypeVal_comp_iff`,
  `IsLocalDiffeomorph.subtypeVal_comp_iff`,
  `isLocalDiffeomorph_inclusion`), merged, in `Boundary/Collar/End.lean`
  and `StableHamiltonian.lean`.
- *Cotangent bundles*: `Geometry/Manifold/Flow/Basic.lean`, merged, which this
  part extends by integral curves as trajectories of the flow (`IsMIntegralCurveOn.sub_mem_flowDomain`,
  `IsMIntegralCurveOn.flowOf_sub_eq`, `TauCeti.eventuallyEq_flowOf_sub_of_isMIntegralCurveOn`,
  `TauCeti.contMDiffAt_of_isMIntegralCurveOn`), in `Liouville/Scaling.lean`.
- *Symplectic neighbourhoods*:
  `Geometry/Manifold/DifferentialForm/Pullback/LocalDiffeomorph.lean`, merged,
  which this part extends by
  `IsLocalDiffeomorph.interior_mextDeriv_mpullback_of_interior_mextDeriv`, in
  `Liouville/Scaling.lean`, and by `TauCeti.RoughForm.pushforwardAt` and
  `TauCeti.mpullback_apply_eq_of_apply_eq_pushforwardAt`, in `Completion.lean`.
- *Hamiltonian flows*: `Geometry/Manifold/MFDeriv/Prod.lean`
  (`MDifferentiableAt.mfderiv_uncurry_apply_mk_zero`), merged, in `Completion.lean`.
- *Moser isotopy*: `Geometry/Symplectic/Manifold/Family.lean`
  (`SmoothTwoForm.isOpen_setOfPred_nondegenerate_bilinFormAt`), merged, in
  `StableHamiltonian.lean`.
- The library: `Geometry/Manifold/IsManifold/InteriorBoundary.lean` of
  *Symplectic vector bundles* (`ModelWithCorners.interiorOpens`,
  `ModelWithCorners.BoundarylessManifold.interior`), merged.
- *Moser isotopy*: `Geometry/Manifold/DifferentialForm/Smooth.lean`
  (`SmoothForm.bilinFormAt_smul`, `SmoothForm.bilinFormAt_neg`,
  `SmoothForm.mpullback_funSMulₗ`, `SmoothForm.funSMulₗ_const`,
  `SmoothForm.funSMulₗ_add`, `SmoothForm.funSMulₗ_one`), only in
  `StableHamiltonian.lean`.
- *Moser isotopy*: `Geometry/Manifold/TubularNeighborhood/RelativePoincare.lean`,
  merged, which issue 1 extends by
  `SmoothEmbedding.exists_mextDeriv_eq_and_mpullback_eq`, only in
  `ContactType.lean`.
- *Moser isotopy*: `Geometry/Manifold/DifferentialForm/Opens.lean`
  (`TauCeti.mpullback_subtypeVal_mextDeriv`), merged, in `ContactType.lean`,
  and (`TauCeti.SmoothForm.restrictInterior`) in `ContactType.lean`, `Collar.lean` and
  `Scaling.lean`.
- *Moser isotopy*: `Geometry/Symplectic/Manifold/Flat.lean`
  (`SmoothTwoForm.IsNondegenerate.interior_flat_inverse_ofSubsingleton`), merged, only in
  `ContactType.lean`.
- Tau Ceti, Liouville and contact type: `IsLiouvilleVectorField`,
  `isLiouvilleVectorField_iff_mextDeriv_interior_eq`, `IsContactType`,
  `isContactType_iff`, `exists_isRestrictedContactType_iff`,
  `isContactFormAt_mpullback`, `IsContactType.isContactForm_mpullback`,
  `IsTransverseAlong`; collars: `mpullback_flowOf_comp_apply_eq_symplectization`,
  `mpullback_flowOf_comp_mextDeriv_apply`, `exists_pos_injOn_flowOf_comp`,
  `exists_continuous_pos_injOn_flowOf_comp`,
  `isLocalDiffeomorphAt_flowOf_comp_of_isTransverseAlong`; domains and
  completions: `IsLiouvilleDomain`, `IsLiouvilleCompletion`.
- Tau Ceti, contact: `SmoothForm.IsContactForm`, `isContactForm_neg_iff`,
  `symplectization`, `isLiouvilleVectorField_symplectization`,
  `IsContactForm.isSymplectic_mextDerivₗ_symplectization`,
  `IsStableHamiltonian`, `characteristicVectorField` with
  `apply_characteristicVectorField`, `interior_characteristicVectorField`,
  `eq_characteristicVectorField_iff`,
  `IsStableHamiltonian.interior_mextDeriv_characteristicVectorField`,
  `IsContactForm.isStableHamiltonian`, `IsContactForm.contMDiff_reebVectorField`
  and `contactFlatEquiv` (adapted), `ContinuousAlternatingMap.pairedWedge_wedgePow_ne_zero_iff`,
  `Module.Dual.isContact_iff_separatingLeft_add_smulRight`,
  `Module.Dual.isContact_iff_nondegenerate_symplectizationForm`.
- Tau Ceti, forms and flows: `mlieDerivForm`,
  `mlieDerivForm_eq_interior_mextDeriv_add`, `RoughForm.interior`,
  `SmoothTwoForm.interiorₗ` with `coe_interiorₗ`,
  `SmoothTwoForm.IsNondegenerate.interiorEquiv`,
  `SmoothForm.mpullback`, `mextDerivₗ`, `flowOf`, `globalFlow`,
  `mpullback_flowOf_apply_of_mextDeriv_interior_eq_zero`,
  `mpullback_flowOf_apply_of_interior_mextDeriv_eq_zero`,
  `IsLocalDiffeomorphAt.contMDiffAt_mpullback_form_iff`,
  `SmoothBundleForm.eq_of_forall_mem_dense`;
  tubular neighbourhoods and relative primitives:
  `SmoothEmbedding.exists_diffeomorph_normalBundle_subset`,
  `SmoothEmbedding.exists_isSmoothForm_relative_primitive`; relative Moser:
  `SmoothTwoForm.exists_diffeomorph_opens_of_eq_along`.
- Tau Ceti, manifolds with boundary: `boundaryChartedSpace`,
  `isManifold_boundary`, `isSmoothEmbedding_subtypeVal_boundary`,
  `IsOutwardPointing` with `isOutwardPointing_iff_tangentCoordChange`,
  `IsOutwardPointingField`, `exists_isOutwardPointingField`,
  `exists_isProductCollarChart_of_mem_boundary`,
  `IsProductCollarChart.diffeomorphProd`, `SmoothCollar` with
  `diffeomorphOpensRange`, `EuclideanHalfSpace.normalIioOpens`,
  `BoundarylessModel` with `interiorChartedSpace` and
  `interiorDiffeomorph`; flows from boundary points:
  `exists_contDiffOn_localFlow_euclideanHalfSpace`,
  `exists_contMDiffOn_localFlow_of_isOutwardPointing_neg`,
  `exists_contMDiffOn_boundaryFlow`; gluing: `chartedSpaceOfIsOpenEmbedding`,
  `TopCat.GlueData.IsCompatible.isManifold`, `TopCat.GlueData.t2Space_iff_forall_nhds`,
  `Diffeomorph.isManifold_chartedSpaceComp`,
  `isCompatible_transContinuousLinearEquiv_iff`.
- Mathlib: `IsMIntegralCurveOn`, the implicit and inverse function
  theorems, `ModelWithCorners.isClosed_boundary_of_finiteDimensional`,
  smooth bump functions on manifolds.

Searched at the pinned versions, in Mathlib, Tau Ceti and this library,
before this part was built: a
converse to `IsContactType.isContactForm_mpullback`, a neighbourhood model
or converse normal form for stable Hamiltonian structures, smoothness of
`characteristicVectorField`, strong fillings, the existence of smooth
collars, and the gluing of an end to a manifold with boundary. None
existed then; the part's own files listed above now provide them. Tau
Ceti's
`Liouville/Completion.lean` and `CylindricalEnd.lean` start from a completion
that is already given.

## Building issues

In this order; each is blocked by the ones listed. All are parts of #480,
*Build the part Liouville structures*.

| # | Issue | Files | Blocked by | Size |
|---|---|---|---|---|
| 1 | Contact type through local Liouville fields | `Liouville/ContactType.lean` | — | 400 |
| 2 | Liouville collars of hypersurfaces, first milestone | `Liouville/Collar.lean` | 1 | 300 |
| 3 | Stable Hamiltonian structures: wedge criterion, Reeb field, invariance | `Contact/StableHamiltonian.lean` | — | 300 |
| 4 | The stable Hamiltonian model and its converse, second milestone | `Contact/StableHamiltonian.lean` | 3 | 500 |
| 5 | Outward fields near the boundary | `Boundary/Collar/Flow/Local.lean` | — | 500 |
| 6 | The collar along an outward field | `Boundary/Collar/Flow/Basic.lean` | 5 | 400 |
| 7 | Strong fillings and their Liouville collar | `Liouville/Filling.lean` | 6 | 400 |
| 8 | Attaching an end along a smooth collar | `Boundary/Collar/End.lean` | — | 600 |
| 9 | The completion: its form, primitive and field | `Liouville/Completion.lean` | 7, 8 | 450 |
| 10 | Symplecticity and the third milestone | `Liouville/Completion.lean` | 9 | 350 |
| 11 | The completion of a Liouville domain is a Tau Ceti completion | `Liouville/Domain.lean` | 10 | 300 |

Issues 1, 3, 5 and 8 can start at once.
The milestones are proved in issues 2, 4 and 10. If issue 5 or 8 exceeds the
size limit, its local chart computations become an issue of their own before
it.

Credit: none of the three milestones follows a statement that the
published errata [McDuffSalamon2019Errata] correct, as far as this design
found; a building issue that finds one cites them.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §3.5: Definition 3.5.27, Proposition 3.5.31, Definition 3.5.32,
  Exercise 3.5.37, Definition 3.5.38 and the completion on p. 148.
* [D. McDuff, D. Salamon, *Errata for Introduction to Symplectic Topology*][McDuffSalamon2019Errata].
* M. Hirsch, *Differential Topology*, Springer GTM 33, 1976, Chapter 4, Theorem 6.1.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218,
  2013, Theorem 9.25.
