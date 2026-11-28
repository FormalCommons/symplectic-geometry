# Symplectic blowup

This is the detailed design of part 61 of `DESIGN.md`, *Symplectic blowup*,
for §7.1 of `atlas/constructing-symplectic-manifolds.md`. It serves seven
milestones: *Kähler forms on the blowup of complex space*, *Symplectic blowup
along a ball*, *Symplectic blowdown*, *Symplectic structure on the almost
complex blowup*, *Normalization of symplectic ball embeddings*, *Uniqueness
of the symplectic blowup* and *Ball embeddings give symplectic forms on the
blowup*.

Sources: McDuff–Salamon [McDuffSalamon2017], §7.1 (Lemma 7.1.11,
Definition 7.1.12, Proposition 7.1.13, the construction (7.1.14),
Definitions 7.1.17–7.1.20, Theorem 7.1.21, Proposition 7.1.22,
Theorem 7.1.23, Corollary 7.1.24, Lemma 7.1.25 by its first proof,
Corollary 7.1.26, (7.1.30) and (7.1.31)), with Lemma A.3.1 for the
profiles; McDuff [McDuff1991], Lemma 2.1 and Corollary 2.2, for the
neighbourhood of the divisor; McDuff–Polterovich [McDuffPolterovich1994],
whom the book follows for Theorem 7.1.21.

All statements about Tau Ceti and Mathlib below were checked against the
pinned versions, Tau Ceti `0651fdbae946` and the Mathlib it pins. Tau Ceti
paths are relative to `.lake/packages/TauCeti/TauCeti/`, and paths of new
files are under `SymplecticGeometry/`.

## Setting and conventions

- **Dimension.** As in `design/complex-blowup.md`, the page's complex
  dimension $n\ge1$ is `n + 1` in Lean, `E := Fin (n + 1) → ℂ`, the divisor
  is `ℙ ℂ E`, the page's "for $n\ge2$" is `1 ≤ n`, and the page's
  coefficient $n-1$ is `n`. Balls are in `StdSpace (Fin (n + 1))`.
- **Manifolds.** The blowups are glued from pieces charted on one model
  space, so the manifold `M` that is blown up is charted on `E`, with
  `IsManifold 𝓘(ℝ, E) ∞ M`, `M : Type` (the pieces of a
  `TopCat.GlueData` share a universe, as *Complex blowup*'s `Blowup c`
  needs), `[T2Space M]`, `[SigmaCompactSpace M]` where Tau Ceti's
  extension theorems need them, and no boundary. A symplectic manifold of
  dimension $2n$ modelled on another space is brought to `E` by the
  library's `Remodel` (`Geometry/Manifold/ModelTransport/Remodel.lean`);
  no statement here takes a general model. The model blowup
  `BlowupModel n` of *Complex blowup* is a complex manifold, and its real
  structure is Tau Ceti's `IsManifold.restrictScalars_of_ne_zero`.
- **Forms.** A symplectic form is `ω : TauCeti.SmoothTwoForm 𝓘(ℝ, E) M`
  with `ω.IsSymplectic`; pull-backs are `SmoothForm.mpullback`. On `E`,
  the book's $\omega_0$ is `ω₀E := (TauCeti.stdComplexPiSymplecticForm
  (Fin (n + 1))).constSmooth`, which `stdForm_complexToRealEuclidean`
  identifies with *Standard model*'s `stdForm` read through
  `complexToRealEuclidean`; Tau Ceti's
  `SymplecticForm.IsSymplectomorphism.mpullback_constSmooth`, applied to
  `isSymplectomorphism_complexToRealEuclidean`, states this for the
  constant forms, so that
  ball embeddings (on `StdSpace`) and the model (on `E`) meet. The
  Fubini–Study form is the library's `fubiniStudyForm n` on `ℙ ℂ E`, in
  which a line has area $\pi$
  (`integralTopForm_mpullback_map_fubiniStudyForm`, for every line). The
  note of the review of #3195 asked for a restriction lemma for that area:
  this theorem is it, and it is merged.
- **Norms and the sets $L(\varepsilon)$.** The norm of `E` is the sup norm,
  so no ball of this part is a ball of `E`. The Euclidean norm of `z : E` is
  `‖complexToRealEuclidean _ z‖`, written $|z|$ below. In the model,
  `BlowupModel.closedNbhd n ε` ($L(\varepsilon)$) and
  `BlowupModel.openNbhd n ε` are the preimages under `blowdown` of
  $\{|z|\le\varepsilon\}$ and $\{|z|<\varepsilon\}$, from the complex
  part's `Blowup/Model.lean` (`design/complex-blowup.md`).
- **Ball embeddings.** A symplectic embedding of $B(r)$ is *Isotopy
  extension*'s `IsSymplecticBallEmbedding ω r ψ`, for
  `ψ : StdSpace (Fin (n + 1)) → M`, and a family of them is
  `IsSymplecticBallFamily ω r e` over `unitInterval`. Read on `E`, $\psi$
  is `ψ ∘ complexToRealEuclidean _`.
- **Cohomology.** A de Rham class is `deRhamCohomology.mk`, and it is
  compared with singular classes through Tau Ceti's `TauCeti.deRhamHom`
  (`Geometry/Manifold/SmoothSingular/SingularCohomology.lean`), as
  `DESIGN.md`'s *Integral classes and line bundles* does. The class $e$ is
  *Complex blowup*'s `Blowup.exceptionalClass c`, with coefficients
  `ULift ℤ`; it enters real statements through the change of coefficients
  $\mathbb Z\to\mathbb R$ that *Poincaré duals of submanifolds* uses. The
  first Chern class of a nondegenerate form is the merged
  `TauCeti.SmoothTwoForm.IsNondegenerate.firstChernClass`.

## Decisions

`DESIGN.md` leaves two questions to this file.

### Smooth families of embeddings and of forms

The page's smooth dependence on $(\lambda,\varepsilon)$ and on $\psi$ is
stated, as every family of `DESIGN.md` is, over `unitInterval`:

- a family of ball embeddings is `IsSymplecticBallFamily ω r ψ`, with
  `ψ : unitInterval × StdSpace (Fin (n + 1)) → M`;
- a family of parameters is a pair of smooth maps
  `λ ε : unitInterval → ℝ` (`ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞`) satisfying the
  page's inequalities at every time;
- a family of forms is *Smooth families*' `IsSmoothFamily (𝓡∂ 1) σ`, for
  `σ : unitInterval → SmoothTwoForm 𝓘(ℝ, E) X`: one smooth form on
  `unitInterval × X` whose slices are the `σ t`.

The page's statement "depends smoothly on $(\psi,\lambda,\varepsilon)$" is
then `Normalized/Family.lean`'s `isSmoothFamily_normalizedBlowupForm`: for
such families, the forms $\tilde\omega_{\psi_t,\lambda_t,\varepsilon_t}$ are
a smooth family. This is what the proofs of Theorem 7.1.23 and
Corollary 7.1.24 use (Moser's argument along a path, and the invariance of
$c_1$ along a path), and the form in which Tau Ceti's and the library's
Moser theorems take their input. No topology on spaces of embeddings is
introduced. In the model, smoothness in the parameters is stated as joint
smoothness of the profile, a function of $(\lambda,\varepsilon,s)$, on the
open set of admissible $(\lambda,\varepsilon)$; the families above follow
by composition.

### `Weight.lean` and `Normalized.lean`

Neither is derived from the other. Both are built on the model of
`Model.lean` and `Profile.lean`:

- the blowup of weight $\lambda$, $\widetilde M_\psi$, is its own glued
  manifold (`Weight/Basic.lean`), since the milestone *Symplectic blowup
  along a ball* is about that space, and *Lefschetz pencils* blows up its
  base points with it;
- the almost complex blowup is *Complex blowup*'s `Blowup c`, with the
  forms $\tilde\omega_{\psi,\lambda,\varepsilon}$ (`Normalized/Basic.lean`);
- Theorem 7.1.21 (ii) is a theorem comparing them
  (`Normalized/Weight.lean`), as in the book: off the lifted ball the map
  is $\psi\circ F_{\lambda,\varepsilon}\circ\psi^{-1}\circ\pi_M$, and on
  $\tilde\psi(L(\varepsilon))$ it is the identity of the model, the two
  agreeing because the gluing map of $\widetilde M_\psi$ is
  $\psi\circ F_\lambda\circ\pi$ and $F_{\lambda,\varepsilon}=F_\lambda$ on
  $B(\varepsilon)$.

Building $\widetilde M_\psi$ from `Blowup c` instead would need a
normalization at $\psi(0)$ only to define a space that the page defines
by gluing, and building `Blowup c`'s forms from $\widetilde M_\psi$ would
lose the fixed almost complex manifold on which Theorem 7.1.23 compares
forms. Both gluings are two-piece gluings; if the constructor of #3359 is
merged first, `Weight/Basic.lean` and `Blowdown.lean` use it.

### Further choices

- **Profiles in the variable $s=|z|^2$.** A radial map is
  $F(z)=f(|z|)z/|z|$, and everything about it is read through
  $h(s)=f(\sqrt s)^2$, which is smooth at $s=0$ when $f$ is
  $\sqrt{\lambda^2+r^2}$ near $0$. The library's profiles are these $h$.
  With $g'(s)=h(s)/s$, $F^*\omega_0$ is the form of the potential
  $g(|z|^2)$ on $\mathbb C^n\setminus0$, and it is Kähler exactly when
  $h'>0$ and $h>0$; this replaces the book's convexity argument by a
  direct computation of the Levi form,
  $g'(s)|v|^2+g''(s)|\langle z,v\rangle|^2$, which is positive since
  $(sg')'=h'>0$. For $h(s)=\lambda^2+s$ this is (7.1.7).
- **The forms $\tilde\omega_{\lambda,\varepsilon}$ are defined on all of
  $L$ at once.** With $q(s)=\int_0^s(h(u)-u-\lambda^2)/u\,du$, smooth on
  `ℝ` and zero for $s\le\varepsilon^2$,
  $\tilde\omega_{\lambda,\varepsilon}=\tilde\omega_\lambda+\pi^*\omega_q$,
  where $\omega_q$ is the form of the potential $q(|z|^2)$, smooth on all
  of `E`. So no form is glued across $Z$, the equality with
  $\tilde\omega_\lambda$ on $L(\varepsilon)$ is the vanishing of $q$, and
  the equality with $\pi^*\omega_0$ outside $L(\lambda+\varepsilon)$ is
  that $\lambda^2\log s+q(s)$ is constant there.
- **Potentials.** The form of a real potential $\phi$ is
  $\tfrac14d(J^*d\phi)$, the real form that the library's
  `Dolbeault/Potential.lean` identifies with $\frac i2\partial\bar\partial\phi$
  (`del_delBar_mapCoeff_ofReal_ofComplexManifold`). Its pull-back along a
  holomorphic map is the form of the pulled-back potential
  (`mpullback_potentialForm`). The Fubini–Study lift on
  $\mathbb C^n\setminus0$ is already of this kind
  (`fubiniStudyLift_eq_del_delBar`, `fubiniStudyPotential`).
- **Normalization (Definition 7.1.17).** A predicate
  `IsNormalizedAt ω J p₀ δ ψ₀`: `ω.Compatible J`, `0 < δ`,
  `IsSymplecticBallEmbedding ω δ ψ₀`, `ψ₀ 0 = p₀`, and $d\psi_0$ is
  complex linear from $J_0$ to $J$ on the open ball. From it,
  `IsNormalizedAt.blowupChart` is the `BlowupChart M p₀` of *Complex
  blowup*, $\psi_0^{-1}$ on $\psi_0(B^\circ(\delta))$ read on `E`, which is
  in the real maximal atlas and $J$-holomorphic, the hypothesis `hJ` of
  *Complex blowup*'s `AlmostComplex.lean`. Every symplectic manifold is
  normalized at every point (Remark 7.1.18 (i)), by the library's
  `IsSymplectic.exists_darbouxChart_stdForm` and Tau Ceti's
  `SmoothTwoForm.Compatible.exists_compatible_eqOn`, with ω unchanged.
- **Hamiltonian maps and isotopic forms.** A Hamiltonian
  symplectomorphism is `Φ.final` for a `TauCeti.Diffeotopy` with *Isotopy
  `IsCompactlySupportedHamiltonian ω` (`Geometry/Symplectic/Flux/CompactSupport.lean`). Two forms are
  *isotopic* when `(Φ.final)^* σ₁ = σ₀` for a `Diffeotopy` `Φ`, and
  *diffeomorphic* when that holds for a diffeomorphism; *joined by a path of
  symplectic forms* is a smooth family over `unitInterval` of symplectic
  forms with the given ends.
- **The volume.** The symplectic volume is Tau Ceti's
  `SmoothTwoForm.liouvilleMeasure` (`Geometry/Symplectic/Manifold/LiouvilleMeasure.lean`),
  so the drop of volume is an identity in `ℝ≥0∞` that holds for
  noncompact `M` too.
- **The blowdown's hypothesis.** The divisor is a
  `TauCeti.SmoothEmbedding f` of `ℙ ℂ E` in `M` with
  `f^*ω = λ² • fubiniStudyForm n` (the page's added hypothesis on
  $(Z,\omega|_Z)$, with the symplectomorphism folded into `f`) and a smooth
  fibrewise isomorphism of its normal bundle with that of the model's
  zero section that preserves the orientations given by the symplectic
  normal forms. For line bundles this is the page's isomorphism with $L$;
  the symplectic one that Tau Ceti's neighbourhood theorem asks for is
  obtained from it by a positive fibrewise rescaling.

## Files

All in `Geometry/Symplectic/Blowup/`, except `Radial.lean`, which is about
$\mathbb C^n\setminus0$ only, and `Ball/Based.lean`, which is about ball
embeddings only. `DESIGN.md` gave `Weight.lean` and `Normalized.lean` as
single files and put the area identity in `Profile.lean`, the neighbourhood
of the divisor in `Blowdown.lean` and Lemma 7.1.25 in `Uniqueness.lean`;
they are split here so that each issue is a few hundred lines, and
`DESIGN.md` is updated to match.

| File | Contents | Issue |
|---|---|---|
| `Geometry/Symplectic/Complex/Radial.lean` | radial potentials and radial maps on $\mathbb C^n\setminus0$ | 1 |
| `Blowup/Model.lean` | $\tilde\omega_\lambda$, its line area, $F_\lambda$ and the shell | 2 |
| `Blowup/Profile.lean` | the profiles and the forms $\tilde\omega_{\lambda,\varepsilon}$ | 3 |
| `Blowup/Area.lean` | the area identity; the first milestone | 4 |
| `Blowup/Weight/Basic.lean` | the blowup $\widetilde M_\psi$ of weight $\lambda$ and its divisor | 5 |
| `Blowup/Weight/Collapse.lean` | the Hopf collapse, the second milestone | 6 |
| `Blowup/DivisorNeighborhood.lean` | a neighbourhood of a divisor is $L(\varepsilon)$ | 7 |
| `Blowup/Blowdown.lean` | the blowdown; the third milestone | 8 |
| `Blowup/Normalized/Basic.lean` | normalizations, lifts, the forms $\tilde\omega_{\psi,\lambda,\varepsilon}$ | 9 |
| `Blowup/Normalized/Weight.lean` | Theorem 7.1.21 (ii) | 10 |
| `Blowup/Normalized/Family.lean` | Theorem 7.1.21 (iii), (vi), (vii) | 11 |
| `Blowup/Normalized/Class.lean` | Theorem 7.1.21 (v); the fourth milestone | 12 |
| `Blowup/BallNormalization.lean` | Proposition 7.1.22; the fifth milestone | 13 |
| `IsotopyExtension/Ball/Based.lean` | Lemma 7.1.25 | 14 |
| `Blowup/Uniqueness.lean` | Theorem 7.1.23, Corollary 7.1.26; the sixth milestone | 15 |
| `Blowup/BallEmbedding.lean` | Corollary 7.1.24; the seventh milestone | 16 |

### `Geometry/Symplectic/Complex/Radial.lean`

Namespace `SymplecticGeometry`, on `puncturedSpace E` with the complex
structure of `E`, for `n : ℕ` and `E := Fin (n + 1) → ℂ`. The radial
potential forms, up to `radialPotentialForm_id`, are stated on `ι → ℂ` for
`[Fintype ι]`.

- `radialPotentialForm ι g hg`: for `g : ℝ → ℝ` and `hg : ContDiffOn ℝ ∞ g (Ioi 0)`, the form
  $\tfrac14d(J^*d(g(|z|^2)))$ on `puncturedSpace (ι → ℂ)`, with
  `radialPotentialForm_def` and `radialPotentialForm_apply`, the explicit
  formula $g'(s)\,\omega_0+g''(s)\,\tfrac i2\partial s\wedge\bar\partial s$
  with $s=|z|^2$, which the computations below read. `radialPotentialForm_id` ($g(s)=s$
  gives $\omega_0$) and `radialPotentialForm_log` ($g=\log$ gives
  `fubiniStudyLift`, by `fubiniStudyPrimitive_eq`).
- `isKahler_radialPotentialForm`: if $g'>0$ and $(sg')'>0$ on `Ioi 0`, the
  form is Kähler for the complex structure of the open subset, by the Levi
  form above.
- `radialMap h`: for `h : ℝ → ℝ` with $h>0$ on `Ioi 0`, the map
  $z\mapsto\sqrt{h(|z|^2)/|z|^2}\,z$ of `puncturedSpace E` into itself;
  `radialMap_apply`, `contMDiff_radialMap`, `norm_radialMap`
  ($|F(z)|^2=h(|z|^2)$), and, for $h'>0$, `radialMapDiffeomorph h`, a
  diffeomorphism onto the shell $\{h(0^+)<|w|^2<h(\infty)\}$.
- `mpullback_radialMap_stdForm`: $F^*\omega_0$ is `radialPotentialForm g`
  for any $g$ with $g'=h/s$; so `isKahler_mpullback_radialMap` for
  $h>0$, $h'>0$. The page's statement with $f$ is the corollary
  `isKahler_mpullback_radialMap_of_profile`, for
  $f:(0,\infty)\to(0,\infty)$ smooth with $f'>0$ and $h(s)=f(\sqrt s)^2$.

### `Blowup/Model.lean`

Namespace `SymplecticGeometry.BlowupModel`, on `BlowupModel n`.

- `ω₀E` as in *Setting*.
- `blowupForm n λ` ($\tilde\omega_\lambda$):
  `blowdown^* ω₀E + λ ^ 2 • pr^* fubiniStudyForm n`, with
  `blowupForm_def`; `isKahler_blowupForm` for `λ ≠ 0`, for the complex
  structure `ofComplexManifold` of the model (closed as a sum of closed
  forms; compatible because $\pi$ and $\mathrm{pr}$ are holomorphic, so
  each term is $J$-invariant and nonnegative on $(v,Jv)$, and
  $(\mathrm{pr},\pi)$ is the holomorphic immersion
  `contMDiff_blowupModel_val`, so the sum is positive),
  and `isSymplectic_blowupForm`.
- `mpullback_zeroSection_blowupForm`: on $Z$ it restricts to
  $\lambda^2\omega_{\mathrm{FS}}$; with
  `integralTopForm_mpullback_map_fubiniStudyForm`,
  `integralTopForm_blowupForm_line`: for `1 ≤ n`, every line of $Z$ has
  area $\pi\lambda^2$.
- `mpullback_blowdownDiffeomorph_symm_blowupForm`: off $Z$,
  $(\pi^{-1})^*\tilde\omega_\lambda$ is `radialPotentialForm` of
  $s+\lambda^2\log s$, so $\pi^*F_\lambda^*\omega_0=\tilde\omega_\lambda$
  there (`mpullback_radialMap_blowdown`, with $h(s)=s+\lambda^2$).
- `shellSymplectomorph n λ ε`: the diffeomorphism
  $F_\lambda\circ\pi$ from `openNbhd n ε \ Z` onto the open shell
  $\lambda<|w|<\sqrt{\lambda^2+\varepsilon^2}$ of `E`, carrying
  $\tilde\omega_\lambda$ to $\omega_0$, and its closed form for
  `closedNbhd`, which the milestone states.

### `Blowup/Profile.lean`

- `blowupProfile λ ε : ℝ → ℝ` ($h_{\lambda,\varepsilon}$): smooth, jointly
  in `(λ, ε, s)` on `{0 < λ} ×ˢ {0 < ε}` (`contDiffOn_blowupProfile`),
  equal to $\lambda^2+s$ for $s\le\varepsilon^2$ and to $s$ for
  $s\ge(\lambda+\varepsilon)^2$, with positive derivative. Construction,
  in the manner of Lemma A.3.1: $h'=1-\beta$ with $0\le\beta<1$ smooth,
  supported in $[\varepsilon^2,(\lambda+\varepsilon)^2]$, of integral
  $\lambda^2$; the interval has length $\lambda^2+2\lambda\varepsilon$, so
  such $\beta$ exist, for instance a mollified step of height
  $\lambda/(\lambda+\varepsilon)$, chosen smoothly in the parameters with
  Tau Ceti's `collaredSmoothTransition`. The issue fixes the formula.
  `ε < 1` is not needed.
- `profileCorrection λ h` ($q$) of a profile `h` with the properties of
  `blowupProfile λ ε` (`IsBlowupProfile λ ε h`), smooth on `ℝ`, zero on
  `Iic (ε ^ 2)`, with `λ ^ 2 * log s + q s` constant on `Ici ((λ + ε) ^ 2)`.
- `profileForm n λ ε h` ($\tilde\omega_{\lambda,\varepsilon}$), with `h`
  defaulting to `blowupProfile λ ε`,
  `blowupForm n λ + blowdown^* (form of the potential q(|z|²))`, with
  `profileForm_def`; for every `h` with `IsBlowupProfile λ ε h`,
  `profileForm_eq_blowupForm_on` (on `closedNbhd n ε`),
  `profileForm_eq_on_compl` (equal to `blowdown^* ω₀E` off
  `closedNbhd n (λ + ε)`), `mpullback_radialMap_profileForm` (off $Z$ it is
  $\pi^*F_{\lambda,\varepsilon}^*\omega_0$), and `isKahler_profileForm`,
  from `isKahler_radialPotentialForm` off $Z$ and `isKahler_blowupForm` on
  `openNbhd n ε`.
- `isSmoothFamily_profileForm`: for smooth `λ ε : unitInterval → ℝ` with
  positive values, `t ↦ profileForm n (λ t) (ε t)` is an `IsSmoothFamily`.

### `Blowup/Area.lean`

- `blowdown_profileForm_area`: for every `h` with `IsBlowupProfile λ ε h`,
  so for `blowupProfile λ ε`, `Ω : Set ℂ` bounded open, `u : ℂ → E`
  `C¹` near every point of `closure Ω` and holomorphic on `Ω`, with
  $|u|>\lambda+\varepsilon$ on `frontier Ω`, finitely many zeros in `Ω` of
  total order `m` (Mathlib's `analyticOrderNatAt`), and
  `ũ : ℂ → BlowupModel n` continuous on `Ω` with `blowdown ∘ ũ = u` there,
  the integral over `Ω` of $u^*\omega_0$ is that of $\tilde u^*\tilde\omega_{\lambda,\varepsilon}$
  (`profileForm n λ ε h`) plus
  $m\pi\lambda^2$. The integrals are Lebesgue integrals over `Ω` of the
  densities $\sigma(\partial_xu,\partial_yu)$. `ũ` is `curveLift u` on `Ω`,
  so holomorphic, by *Complex blowup*'s `eqOn_curveLift_of_blowdown_comp`
  (`Lift.lean`), and `continuousOn_curveLift` with `blowdown_curveLift`
  gives its existence.
- Proof: off the zeros the difference of the densities is
  $\tfrac14\Delta(\phi\circ u)$ with $\phi(s)=s-g(s)$, constant near
  `frontier Ω`, and $\phi\circ u=-\lambda^2m_j\log|t-t_j|^2+$ smooth at a
  zero of order $m_j$; the planar identity
  `setIntegral_laplacian_eq_of_log_poles` (`LogarithmicPole.lean`) then gives
  $\int_\Omega\Delta(\phi\circ u)=4\pi\lambda^2m$.
- **Milestone** `kahler_blowupModel`: the conjunction of
  `isKahler_blowupForm` with the line area, `isKahler_mpullback_radialMap_of_profile`,
  `mpullback_radialMap_blowdown` with `shellSymplectomorph`, the
  properties of `profileForm` with `isSmoothFamily_profileForm`, and
  `blowdown_profileForm_area`. Its docstring ends with the line Milestone:
  *Kähler forms on the blowup of complex space*.

### `Blowup/Weight/Basic.lean`

Namespace `SymplecticGeometry.WeightBlowup`, for `M` as in *Setting*,
`ω` symplectic, `0 < λ`, `0 < ε`, and `ψ` with
`IsSymplecticBallEmbedding ω (√(λ ^ 2 + ε ^ 2)) ψ`; the page's extension of
$\psi$ to the larger ball is this hypothesis, and *Isotopy extension*'s
`exists_lt_isSymplecticBallEmbedding_eqOn` provides it from an embedding of
$B(\lambda)$.

- `IsSymplecticBallEmbedding.toPartialDiffeomorph`: on the open ball a symplectic
  ball embedding is an open smooth embedding, a `PartialDiffeomorph`
  (injective, with injective differential by `injective_mfderiv`, in equal
  dimension). It goes in *Isotopy extension*'s `Ball/Basic.lean` if that
  file has no such lemma when the issue starts; the issue searches first.
- `gluingDiffeomorph hψ hλ hε`, for `hλ : 0 ≤ λ` and `hε : 0 < ε`: two
  pieces, the open set `(ψ '' closedBall 0 λ)ᶜ` of `M`
  and `openNbhd n ε`, glued along `openNbhd n ε \ Z` and
  $\psi(\{\lambda<|w|<\sqrt{\lambda^2+\varepsilon^2}\})$ by
  $(\ell,z)\mapsto\psi(F_\lambda(z))$, the page's
  $\psi(\sqrt{1+\lambda^2/|z|^2}\,z)$, that is
  `ψ ∘ shellSymplectomorph`; `WeightBlowup hψ hλ hε`, the `GluedAlong` of
  its inverse, with
  `inl`, `inr`, `inl_eq_inr_iff`, the charted space and
  `IsManifold 𝓘(ℝ, E) ∞` by Tau Ceti's `IsCompatible.isManifold`;
  `T2Space` (a point of $Z$ and a point $x\notin\psi(B(\lambda))$ are
  separated by $L(\delta)$ with $\sqrt{\lambda^2+\delta^2}$ below the
  radius of $\psi^{-1}x$, or by a neighbourhood missing the compact
  $\psi(B(\sqrt{\lambda^2+\delta^2}))$), `SecondCountableTopology`.
- `form ψ λ ε` ($\tilde\omega_\psi$): $\omega$ on the first piece and
  `blowupForm n λ` on the second, which agree on the overlap by
  `shellSymplectomorph`; `mpullback_inl_form`, `mpullback_inr_form`,
  `isSymplectic_form`. The form is glued by `GluedAlong.gluedForm`.
- `divisor ψ λ ε`: `inr ∘ zeroSection`, a `TauCeti.SmoothEmbedding` with
  `mpullback_divisor_form` ($\lambda^2\omega_{\mathrm{FS}}$), so a
  symplectic submanifold (`IsSymplecticSubmanifoldEmbedding`), and
  `normalSpaceDivisorEquiv`, its normal bundle as $L$, from *Complex
  blowup*'s `normalSpaceZeroSectionEquiv` (`Tautological.lean`) through
  `inr`.
- `complDivisorSymplectomorph`: the complement of $Z$ is
  symplectomorphic to $M\setminus\psi(B(\lambda))$, as open subsets,
  through `inl` and the gluing map.

### `Blowup/Weight/Collapse.lean`

- `collapseMap hψ hλ hε : ((ψ '' ball 0 λ)ᶜ : Set M) → WeightBlowup hψ hλ.le hε`, for `0 < λ`:
  `inl` off $\psi(B(\lambda))$, and $\psi(w)\mapsto$ `divisor [w]` for
  $|w|=\lambda$; continuous, surjective, closed (proper, from a closed
  subset of `M`), so a quotient map; its fibres are the points off the
  sphere and the Hopf circles of $\psi(\partial B(\lambda))$, by
  `sphereHopf_eq_sphereHopf_iff` (Hopf circles of the sphere of radius
  $\lambda$, after scaling).
- `collapseHomeomorph`: the homeomorphism from the quotient of
  `(ψ '' ball 0 λ)ᶜ` by `Setoid.ker (collapseMap hψ hλ hε)`, the relation
  "equal, or both on the sphere with the same `sphereHopf`",
  onto `WeightBlowup hψ hλ.le hε`.
- `liouvilleMeasure_form_add`: the Liouville measure of the blowup plus
  the Lebesgue measure of $B(\lambda)$, its Liouville measure for
  $\omega_0$, is that of `M`, in `ℝ≥0∞`, for any `σ` and `0 ≤ λ`; it is in
  `Blowup/Weight/Volume.lean`. $Z$ is null in the charts of the model,
  `inl` carries the Liouville measure of $M\setminus\psi(B(\lambda))$ onto the
  complement of $Z$, and $\psi$ carries that of $\omega_0$ on $B(\lambda)$ to that of
  $\omega$ (`IsSymplecticBallEmbedding.liouvilleMeasure_image`).
- **Milestone** `WeightBlowup.isSymplectic_form_and_divisor`: the conjunction
  of `isSymplectic_form`, the divisor statements, `collapseHomeomorph` and
  `liouvilleMeasure_form_add`. Its docstring ends with the line Milestone:
  *Symplectic blowup along a ball*.

### `Blowup/DivisorNeighborhood.lean`

For `f : SmoothEmbedding (ℙ ℂ E) M` and the normal bundle isomorphism of
*Decisions*.

- `exists_symplectomorphism_blowupModel`: there are `0 < ε` and a
  symplectomorphism of an open neighbourhood of `range f` onto
  `openNbhd n ε` with `blowupForm n λ`, sending `f` to `zeroSection`, stated
  as a `PartialDiffeomorph` with target `openNbhd n ε` that is symplectic on its
  source. By
  `HasSymplecticTangentImages.exists_symplectomorphism_opens_of_finrank_eq_two`
  (`Geometry/Symplectic/Neighborhood/CodimTwo.lean`), which rescales the normal
  isomorphism to a symplectic one, applied to `f` and
  `zeroSectionRealEmbedding n` with $\tilde\omega_\lambda$; then shrink to `openNbhd n ε`
  inside the image, by compactness of $Z$ (McDuff, Lemma 2.1 and
  Corollary 2.2). For `n = 0`, $Z$ is a point and this is Darboux's
  theorem, with $\lambda$ as data, as the page notes.

### `Blowup/Blowdown.lean`

- `DivisorBlowdown hΨ hf hl hε`, for a partial diffeomorphism `Ψ` from `M` to
  the model with target `openNbhd n ε` (`hΨ`) and `Ψ (f q) = zeroSection q`
  (`hf`), taken as data (`exists_symplectomorphism_blowupModel` gives one):
  the manifold glued from `(range f)ᶜ` and the open ball
  $B^\circ(\sqrt{\lambda^2+\varepsilon^2})$ of `E` (Euclidean norm), along
  `Ψ.source ∖ Z` and the open shell, through `Ψ` and `shellSymplectomorph`; its form
  ($\omega$ and $\omega_0$), `isSymplectic_blowdownForm`, and the ball
  embedding `blowdownBall`, an `IsSymplecticBallEmbedding` of radius
  $\lambda$ (indeed of any radius below $\sqrt{\lambda^2+\varepsilon^2}$),
  whose image replaces $Z$: the complement of `blowdownBall '' closedBall 0 λ`
  is symplectomorphic to `(range f)ᶜ`.
- `weightBlowup_blowdown`: blowing up the blowdown along `blowdownBall`
  with weight $\lambda$ gives a manifold symplectomorphic to `M`, sending
  its divisor to `f`; and `blowdown_weightBlowup`: blowing down the
  divisor of `WeightBlowup hψ hλ hε` gives `M` back, symplectomorphic off
  $\psi(B(\lambda))$ and carrying `blowdownBall` to `ψ` near $B(\lambda)$.
- **Milestone** `exists_blowdown`: the conjunction of
  `exists_symplectomorphism_blowupModel` and the two statements above. Its
  docstring ends with the line Milestone: *Symplectic blowdown*. The
  page's remark that the result is independent of $\varepsilon$ and of the
  identification is not a milestone and is not proved.

### `Blowup/Normalized/Basic.lean`

Namespace `SymplecticGeometry`, for `M` as in *Setting*, `ω`, `J`, `p₀`,
`δ`, `ψ₀` with `hN : IsNormalizedAt ω J p₀ δ ψ₀`, and `c := hN.blowupChart`.

- `IsNormalizedAt` and its API (`isNormalizedAt_def`, `compatible`,
  `isSymplecticBallEmbedding`, `map_zero`, `mfderiv_comp_stdComplexStructure`),
  `IsNormalizedAt.blowupChart`, `blowupChart_mem_maximalAtlas`,
  `blowupChart_isHolomorphic` (the `hJ` of *Complex blowup*), and
  `exists_isNormalizedAt` (Remark 7.1.18 (i), as in *Decisions*).
- The almost complex blowup (Definition 7.1.19) is
  `(Blowup c, Blowup.almostComplexStructure c J _)` of *Complex blowup*'s
  `AlmostComplex.lean`; no new type.
- `IsNormalizedBallEmbedding hN ψ r λ ε` (Definition 7.1.20 with the page's
  constants): `IsSymplecticBallEmbedding ω r ψ`, `0 < λ`, `0 < ε < 1`,
  `λ + ε < r`, `ε < δ`, and `EqOn ψ ψ₀ (closedBall 0 ε)`.
- `ballLift hψ` ($\tilde\psi$), from `openNbhd n r` to `Blowup c`: `inr`
  near $Z$ (where $\psi=\psi_0$) and `inl ∘ ψ ∘ blowdown` off $Z$, which
  agree; an open embedding, a `PartialDiffeomorph`, with
  `blowdown_ballLift`.
- `normalizedBlowupForm hψ` ($\tilde\omega_{\psi,\lambda,\varepsilon}$):
  $(\tilde\psi^{-1})^*$`profileForm n λ ε` on the image of `ballLift`, and
  `Blowup.blowdown c ^* ω` off `ballLift '' closedNbhd n (λ + ε)`, which
  agree on the overlap by `profileForm_eq_on_compl` and $\psi^*\omega=\omega_0$;
  `normalizedBlowupForm_eq_on_ballLift`, `normalizedBlowupForm_eq_on_compl`,
  `isSymplectic_normalizedBlowupForm`, and `eq_normalizedBlowupForm`: any
  form with these two restrictions is it (the two open sets cover).
- (i) `normalizedBlowupForm_eq_blowupForm_on`: on `ballLift '' closedNbhd n ε`
  it is $(\tilde\psi^{-1})^*\tilde\omega_\lambda$.
- (iv) `compatible_normalizedBlowupForm`: if $d\psi$ is complex linear
  from $J_0$ to $J$ on $B(\lambda+\varepsilon)$, the form is compatible
  with $\tilde J$: on the lifted ball `ballLift` is $\tilde J$-holomorphic
  and `profileForm` is Kähler, and elsewhere $\tilde J$ is the pull-back
  of $J$ (`mfderiv_blowdown_comp_almostComplexStructure`).

### `Blowup/Normalized/Weight.lean`

- (ii) `normalizedBlowupSymplectomorph hψ hh hε' hε'ε`: a diffeomorphism from
  `Blowup c` onto `WeightBlowup hψ' hλ hε'`, for a profile `h` with
  `hh : IsBlowupProfile λ ε h` and `0 < ε' ≤ ε` (so that
  $\sqrt{\lambda^2+\varepsilon'^2}\le\lambda+\varepsilon<r$), built as in
  *Decisions*, with `F_{λ,ε} = radialMap h`;
  `isSymplectomorphism_normalizedBlowupSymplectomorph`: it carries
  `normalizedBlowupForm hψ h` to `WeightBlowup.form`. It is glued from
  the two pieces of `WeightBlowup` by `GluedAlong.descDiffeomorph`.

### `Blowup/Normalized/Family.lean`

- (iii) `isSmoothFamily_normalizedBlowupForm`: for a family of normalized
  embeddings (an `IsSymplecticBallFamily ω r ψ` whose slices agree with
  `ψ₀` on `closedBall 0 (ε t)`) and smooth `λ`, `ε` satisfying the
  inequalities at every time, the forms are an `IsSmoothFamily`, by
  `isSmoothFamily_profileForm` and the joint smoothness of the lifts.
- (vi) `exists_path_compatible`: the form is joined, by a smooth family of
  symplectic forms, to one compatible with $\tilde J$. Following the book:
  shrink $(\lambda,\varepsilon)$ to $(\lambda',\varepsilon')$ with
  $\lambda'+\varepsilon'<\varepsilon$, where $\psi=\psi_0$ is holomorphic,
  and apply (iv); the classes change along the path, as the page allows.
- (vii) `exists_diffeotopy_normalizedBlowupForm_of_profile`: two profiles
  with the properties of `blowupProfile` give forms related by a
  compactly supported diffeotopy, by Moser's argument along the convex
  path of profiles, whose forms differ by $d$ of compactly supported
  primitives (`TauCeti.SmoothTwoForm.exists_isotopy_mpullback_eq_of_isCompact`,
  `Geometry/Symplectic/Manifold/Moser.lean`). So `normalizedBlowupForm`
  takes the profile as an argument, defaulting to `blowupProfile`; the
  issue of `Normalized/Basic.lean` sets this up.

### `Blowup/Normalized/Class.lean`

- (v) `deRhamHom_normalizedBlowupForm`: the image under `deRhamHom` of
  $[\tilde\omega_{\psi,\lambda,\varepsilon}]$ is $\pi_M^*$ of that of
  $[\omega]$ plus $\pi\lambda^2e$, as the relative version of the library's
  $e$, the real relative dual class, pairs to $-1$ with a positive normal
  disc
  (`singularKronecker_realRelDualClass_relClass_of_hasFDerivAt_of_eq_comp`;
  `ERRATA.md`). Proof: on the complement of $Z$ the
  difference with $\pi_M^*\omega$ is $d$ of a form supported in the lifted
  ball, so the difference class restricts to zero there and lifts to
  $H^2(\widetilde M,\widetilde M\setminus Z)$, where it is a multiple of
  the Thom class; the multiple is read on a normal slice of $Z$
  (*Poincaré duals of submanifolds*' `eq_relDualClassOf_iff_forall_slice`),
  a disc in a line of the model, where it is $-\int\lambda^2\alpha_{\mathrm{FS}}$
  over the boundary circle, $-\pi\lambda^2$. This works for every
  $n\ge1$, also when $Z$ is a point.
- **Milestone** `normalizedBlowupForm_spec`: the conjunction of
  `eq_normalizedBlowupForm` with its two restrictions, (i)–(vii). Its
  docstring ends with the line Milestone: *Symplectic structure on the
  almost complex blowup*.

### `Blowup/BallNormalization.lean`

For `M` connected, without boundary, Hausdorff and σ-compact, `0 < r`.

- `exists_hamiltonian_comp_eqOn`, in
  `Geometry/Symplectic/IsotopyExtension/Ball/Homogeneity.lean`: for ball
  embeddings `ψ₀ ψ₁` of radius
  `r`, a Hamiltonian diffeotopy `Φ` with `Φ.final ∘ ψ₀ = ψ₁` on a ball
  about $0$, fixing `p₀` at all times when `ψ₀ 0 = ψ₁ 0 = p₀`. Proof: a
  smooth path of centres is a radius-zero `IsSymplecticBallFamily`
  (`IsSymplecticBallFamily.of_path`), and
  `IsSymplecticBallFamily.exists_hasHamiltonian_extension` with `r₀ = 0`
  gives `Φ` and the ball.
- `exists_family_comp_eqOn`: for an `IsSymplecticBallFamily ω r ψ` with
  `ψ t 0 = p₀` and $\psi_1=\psi_0$ near $0$, a jointly smooth family `χ` of
  symplectomorphisms of $B(r)$ with `χ 0 = χ 1 = id` and
  $\psi_t\circ\chi_t=\psi_0$ near $0$, from the loop
  $\Psi_t=d(\psi_0^{-1}\circ\psi_t)(0)$ of $\mathrm{Sp}(2n)$ and its
  polar decomposition (Tau Ceti's `SymplecticGroup.polarUnitary_mem`,
  `Units.polarUnitary`), following the book's proof. A symplectomorphism
  of $B(r)$ is an `IsSymplecticBallEmbedding` for `ω₀` of radius `r` that
  maps `closedBall 0 r` onto itself.
- **Milestone**: the docstring of `exists_family_comp_eqOn` ends with the
  line Milestone: *Normalization of symplectic ball embeddings*, and names
  `exists_hamiltonian_comp_eqOn` for the first part.

### `Geometry/Symplectic/IsotopyExtension/Ball/Based.lean`

- `exists_based_family_of_family` (Lemma 7.1.25, first proof): for `M`
  simply connected (`SimplyConnectedSpace`), two ball embeddings of radius
  $\lambda$ centred at `p₀` that are joined by an `IsSymplecticBallFamily`
  are joined by one whose centre stays at `p₀`: the loop of centres is
  null-homotopic, a smooth null-homotopy moves the centres back by
  Hamiltonian diffeotopies, as in `exists_hamiltonian_comp_eqOn`.
  Surjectivity on components, which the page's note derives from moving
  the centre, is `exists_hamiltonian_comp_eqOn` itself, and is stated as
  the corollary `exists_based_family_of_exists_family` for completeness
  only if a later proof needs it.

### `Blowup/Uniqueness.lean`

For two normalized embeddings `hψ₁ : IsNormalizedBallEmbedding hN ψ₁ r₁ λ₁ ε₁`
and `hψ₂`.

- `exists_path_normalizedBlowupForm`: the two forms are joined by a smooth
  family of symplectic forms: shrink both to $(\lambda',\varepsilon')$
  inside the ball where $\psi_1=\psi_2=\psi_0$, where the forms agree
  (`isSmoothFamily_normalizedBlowupForm`).
- `deRhamHom_normalizedBlowupForm_eq_iff`: the classes agree if $\lambda_1=\lambda_2$, and only
  then when `1 ≤ n` (the real image of the exceptional class is nonzero,
  `Blowup.singularCohomologyRealImageAddMonoidHom_exceptionalClass_ne_zero`)
  or, in `deRhamHom_normalizedBlowupForm_eq_iff_of_compactSpace`, when `n = 0`
  and `M` is compact (total area, from
  `liouvilleMeasure_form_add` through `Normalized/Weight.lean`).
- `exists_diffeotopy_of_based_family`: if $\lambda_1=\lambda_2=\lambda$ and
  the restrictions to $B(\lambda)$ are joined by a family with centre
  `p₀`, the forms are isotopic: normalize the family
  (`exists_family_comp_eqOn`), and Moser's argument along the resulting
  path of cohomologous forms, which vary on a compact set.
- `exists_diffeomorph_of_family`: if they are joined by a family that moves
  the centre, the forms are diffeomorphic, by `exists_hamiltonian_comp_eqOn`
  and the lift of the final Hamiltonian diffeomorphism.
- `exists_diffeotopy_of_simplyConnected` (Corollary 7.1.26): for simply
  connected `M`, `exists_based_family_of_family` and
  `exists_diffeotopy_of_based_family`.
- **Milestone**: the docstring of `exists_diffeotopy_of_based_family` ends
  with the line Milestone: *Uniqueness of the symplectic blowup*, and names
  the other four.

### `Blowup/BallEmbedding.lean`

For `M` connected, second countable and σ-compact, `hN`, `0 < λ` and
`IsSymplecticBallEmbedding ω λ ψ`.

- **Milestone** `exists_symplectic_class_firstChernClass`: there is a
  symplectic form $\tau$ on `Blowup c` with
  `deRhamHom [τ] = π_M^* (deRhamHom [ω]) + π λ² e` (the sign of the
  library's `e`, `ERRATA.md`) and
  `firstChernClass τ = π_M^* (firstChernClass ω) - n • e`. Proof: extend
  $\psi$ (`exists_lt_isSymplecticBallEmbedding_eqOn`), normalize it
  (`exists_hamiltonian_comp_eqOn`, which preserves `ω`), take
  `normalizedBlowupForm` and (v); for $c_1$, (vi) joins it to a
  $\tilde J$-compatible form through nondegenerate forms, Tau Ceti's
  `firstChernClass_mpullback_prodMk_eq` and `firstChernClass_eq_of_compatible`
  give $c_1(\tilde J)$, and *Complex blowup*'s `Blowup.firstChernClass_tangent`
  gives the formula, with $c_1(\omega)=c_1(J)$ on `M`. Its docstring ends
  with the line Milestone: *Ball embeddings give symplectic forms on the
  blowup*.

## What the part uses

- *Complex blowup* (not yet merged): `Model.lean` (#3375: `BlowupModel`,
  `pr`, `blowdown`, `zeroSection`, `blowdownDiffeomorph`), `Tautological.lean`
  (#3377: `zeroSectionEmbedding`, `normalSpaceZeroSectionEquiv`, the source
  of $\nu_Z\cong L$), `Lift.lean` (#3379: `curveLift`, for `Area.lean`),
  `Basic.lean` (#3381: `BlowupChart`, `Blowup c`, `Blowup.blowdown`,
  `Blowup.isCompatible_real`), `AlmostComplex.lean` (#3385),
  `ExceptionalClass.lean` (#3392) and `ChernClass.lean` (#3395).
- The library: `fubiniStudyForm` with `isKahler_fubiniStudyForm`,
  `integralTopForm_mpullback_map_fubiniStudyForm`, `fubiniStudyPrimitive`,
  `fubiniStudyLift_eq_del_delBar`, `sphereHopf` and
  `sphereHopf_eq_sphereHopf_iff`; `Dolbeault/Potential.lean`;
  *Isotopy extension*'s `Ball/` (`IsSymplecticBallEmbedding`,
  `IsSymplecticBallFamily`, `exists_ballEmbedding_extension_and_hasHamiltonian_extension`,
  `exists_hasHamiltonian_extension`), `IsCompactlySupportedHamiltonian`
  and `exists_contDiff_path_symplecticGroup`; *Smooth families*' `IsSmoothFamily`;
  *Moser isotopy*; `radialAngularForm`; `Remodel`.
- Tau Ceti: the gluing of manifolds (`Geometry/Manifold/Gluing/`),
  `exists_standardDarbouxChart_of_isInteriorPoint`,
  `Compatible.exists_compatible_eqOn`, `SmoothTwoForm.IsKahler`,
  `exists_symplectomorphism_opens`, `liouvilleMeasure`, `deRhamHom`,
  `IsNondegenerate.firstChernClass` with its invariance lemmas,
  `exists_isotopy_mpullback_eq_of_isCompact`, `SymplecticGroup.polarUnitary_mem`,
  Stokes (`integralTopForm_mextDeriv_eq_zero`), `collaredSmoothTransition`.
- Mathlib: `analyticOrderAt`, `SimplyConnectedSpace`,
  `IsLocalDiffeomorph.diffeomorphOfBijective`.
- Other parts, not yet merged: *Poincaré duals of submanifolds* (#3279,
  through `ExceptionalClass.lean`, and its slice lemma for `Class.lean`).

## Building issues

In this order. Each issue is blocked by the ones listed, and all are
sub-issues of #3285, *Build the part Symplectic blowup*. Issues of
*Complex blowup* are given by number; where an issue waits for another
part, it waits for the building issue that adds the file named. Sizes are
estimates.

| # | Issue | Files | Blocked by | Size |
|---|---|---|---|---|
| 1 | Radial potentials and radial maps on $\mathbb C^n\setminus0$ | `Complex/Radial.lean` | — | 400 |
| 2 | The Kähler forms $\tilde\omega_\lambda$ on the model blowup | `Blowup/Model.lean` | 1; #3375 | 400 |
| 3 | Profiles and the forms $\tilde\omega_{\lambda,\varepsilon}$ | `Blowup/Profile.lean` | 2 | 450 |
| 4 | The area identity; *Kähler forms on the blowup of complex space* | `Blowup/Area.lean` | 3; #3379 | 450 |
| 5 | The blowup of weight $\lambda$ | `Blowup/Weight/Basic.lean` | 2; #3377 | 650 |
| 6 | Hopf collapse and volume; *Symplectic blowup along a ball* | `Blowup/Weight/Collapse.lean` | 5 | 350 |
| 7 | A neighbourhood of a divisor | `Blowup/DivisorNeighborhood.lean` | 2; #3377 | 350 |
| 8 | The blowdown; *Symplectic blowdown* | `Blowup/Blowdown.lean` | 5, 7 | 600 |
| 9 | Normalizations, lifts and the blowup forms | `Blowup/Normalized/Basic.lean` | 3; #3381, #3385 | 600 |
| 10 | The comparison with the blowup of weight $\lambda$ | `Blowup/Normalized/Weight.lean` | 5, 9 | 300 |
| 11 | Families of blowup forms | `Blowup/Normalized/Family.lean` | 9 | 450 |
| 12 | The class of the blowup form; *Symplectic structure on the almost complex blowup* | `Blowup/Normalized/Class.lean` | 10, 11; #3392 | 350 |
| 13 | *Normalization of symplectic ball embeddings* | `Blowup/BallNormalization.lean` | — | 500 |
| 14 | Based families of ball embeddings | `IsotopyExtension/Ball/Based.lean` | 13 | 300 |
| 15 | *Uniqueness of the symplectic blowup* | `Blowup/Uniqueness.lean` | 6, 12, 14 | 500 |
| 16 | *Ball embeddings give symplectic forms on the blowup* | `Blowup/BallEmbedding.lean` | 12, 13; #3395 | 250 |

Issues 1 and 13 can start once this design is merged. Issue 15 waits for 6
only for the total area of a closed surface. *Lefschetz pencils* needs
issues 5 and 10 (`design/lefschetz-pencils.md`, issue 9).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1 and Lemma A.3.1.
* [D. McDuff, *Blow ups and symplectic embeddings in dimension 4*][McDuff1991],
  Lemma 2.1 and Corollary 2.2.
* [D. McDuff, L. Polterovich, *Symplectic packings and algebraic geometry*][McDuffPolterovich1994].
