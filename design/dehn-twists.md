# Dehn twists

The detailed design of part 55 of `DESIGN.md`, *Dehn twists*. It proves
the milestone *Dehn twist along a framed Lagrangian sphere* of
`atlas/symplectic-fibrations.md`. The model twist on $T^*S^n$ follows
Seidel [Seidel2003], Lemma 1.8 and equation (1.7) (arXiv version 2), and
the twist along a framed sphere follows the paragraph before Proposition
1.11 there. For $n=2$ the construction and the independence of the choices
are Lemmas 2.1 and 2.2 and Proposition 2.3 of Seidel's thesis
[Seidel1997Thesis], repeated in [Seidel2008], §1a. McDuff–Salamon
[McDuffSalamon2017] describe the compactly supported twist on p. 270 and
prove the Lagrangian neighbourhood theorem as Theorem 3.4.13. Arnold
[Arnold1995] introduced the twist on $T^*S^n$. The smoothness of a smooth even
function as a function of $t^2$ is Whitney's theorem (H. Whitney,
*Differentiable even functions*, Duke Mathematical Journal 10 (1943),
159–160).

All names below are in the namespace `SymplecticGeometry` unless they are
written with another one. Paths of new files are under `SymplecticGeometry/`;
Tau Ceti paths are relative to `.lake/packages/TauCeti/TauCeti/`. Tau Ceti
declarations were checked at the pinned commit `c9d170eed5a8`. Throughout,
`E := EuclideanSpace ℝ (Fin (n + 1))`, `Sⁿ := Metric.sphere (0 : E) 1` with
Mathlib's manifold structure modelled on `𝓡 n`, and
`T*Sⁿ := TauCeti.CotangentBundle (𝓡 n) Sⁿ`, with Tau Ceti's Liouville form
`λ := TauCeti.CotangentBundle.liouvilleForm` and its form
`TauCeti.CotangentBundle.symplecticForm`, which is $-d\lambda$
(`symplecticForm_eq_neg_mextDeriv`). The manifold `M` is modelled on
`I : ModelWithCorners ℝ F H` with `[FiniteDimensional ℝ F]`,
`[I.Boundaryless]`, `[T2Space M]`, `[SecondCountableTopology M]`, and
carries `ω : TauCeti.SmoothTwoForm I M` with `hω : ω.IsSymplectic`.

## What exists, and what the part adds

Tau Ceti and the library already have:

- **The round sphere.** The round metric `TauCeti.sphereRoundMetric` and the
  isometry `TauCeti.sphereTangentEquiv x : TangentSpace (𝓡 n) x ≃ₗᵢ[ℝ] (ℝ ∙ x)ᗮ`
  (`Geometry/Manifold/Riemannian/Sphere/Basic.lean`), great circles with
  `TauCeti.isGeodesicCurve_sphereGreatCircle` and
  `TauCeti.antiperiodic_sphereGreatCircle` (`Sphere/Geodesic.lean`), and
  the inclusion `TauCeti.orthogonalToDiffSphere n m : O(n+1) →* Diff(Sⁿ)`
  (`Geometry/Diffeomorphism/Sphere.lean`).
- **Cotangent bundles.** Cotangent lifts `Diffeomorph.cotangent`
  (`Geometry/Manifold/Diffeomorph/Cotangent.lean`), which preserve `λ`
  (`Diffeomorph.mpullback_cotangent_liouvilleForm`,
  `Geometry/Symplectic/Cotangent/Bundle/Lift.lean`); the pullback of `λ`
  along a map over a given base map
  (`TauCeti.CotangentBundle.mpullback_liouvilleForm_apply_of_proj_comp_eq`)
  and along a fibrewise rescaling
  (`mpullback_liouvilleForm_apply_of_eq_smul`, `Cotangent/Bundle/Liouville.lean`);
  smooth maps into `T*M` built from a covector field
  (`TauCeti.CotangentBundle.contMDiff_mk_comp_mfderiv`); the unit codisc
  bundle `TauCeti.CotangentBundle.codiscBundle` of a Riemannian manifold,
  compact over a compact base (`isCompact_codiscBundle`,
  `Cotangent/Bundle/Codisc.lean`); the kinetic energy
  $|p|^2/2$ and its cogeodesic flow (`Cotangent/Bundle/Cogeodesic.lean`,
  `GeodesicSpray.lean`). Tau Ceti has no Hamiltonian flow of $|p|$. Its
  planar twist maps (`TauCeti.hamiltonianFlow_radialHamiltonian`,
  `Hamiltonian/RadialTwist.lean`) rotate $\mathbb C$ about a point, the
  Hamiltonian being a function of the distance to it. They are not maps of
  a cotangent bundle, so the model does not use them.
- **Fibrewise dilations.** Multiplication of the fibres of a vector bundle
  by a nowhere-zero smooth function, as a diffeomorphism
  `TauCeti.vectorBundleScalarDiffeomorph`, with `ContMDiff.smul_totalSpace`
  and the images of the sets `{v | ‖v‖ ≤ r}`
  (`TauCeti.vectorBundleScalarDiffeomorph_image_setOf_norm_le`,
  `Geometry/Manifold/VectorBundle/Scalar.lean`); on a cotangent bundle the
  dilation by `c ≠ 0` pulls `λ` back to `c • λ` and `symplecticForm` to
  `c • symplecticForm`
  (`TauCeti.CotangentBundle.mpullback_vectorBundleScalarDiffeomorph_liouvilleForm`,
  `mpullback_vectorBundleScalarDiffeomorph_symplecticForm`,
  `Geometry/Symplectic/Cotangent/Bundle/Fiberwise.lean`); and the family
  `(v, t) ↦ t • v` for `t ∈ [0, 1]`, smooth on the cylinder
  (`TauCeti.vectorBundleFiberScaling`, `contMDiff_vectorBundleFiberScaling`,
  `Geometry/Manifold/VectorBundle/FiberScaling.lean`). Below, $m_c$ is the
  dilation by $c$, and $N=m_{-1}$ is the fibrewise negation.
- **Hamiltonian dynamics.** `TauCeti.SmoothTwoForm.hamiltonianVectorField_comp`
  ($X_{\varphi\circ f}=\varphi'(f)X_f$, `Hamiltonian/Manifold.lean`). The
  library's merged *Hamiltonian flows* has `TauCeti.Diffeotopy.IsGeneratedBy`,
  `IsCompactlySupportedHamiltonian` and
  `TauCeti.Diffeotopy.exists_isCompactlySupportedHamiltonian` (a smooth
  compactly supported time-dependent function generates a compactly
  supported Hamiltonian diffeotopy that is the identity off the support,
  `Flux/CompactSupport.lean`).
- **Neighbourhoods and isotopies.** The merged Lagrangian neighbourhood
  theorem
  `TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.exists_symplectomorphism_cotangent`
  (`Geometry/Symplectic/Neighborhood/Lagrangian.lean`), existence only; the
  merged neighbourhood extension of isotopies of submanifolds
  `TauCeti.SmoothIsotopy.exists_isSymplectic_extension_of_mpullback_eq`
  (`IsotopyExtension/Submanifold.lean`), with
  `TauCeti.SmoothIsotopy.IsSymplectic` (`IsotopyExtension/Velocity.lean`);
  Tau Ceti's extension of a compactly supported diffeomorphism of an open
  set by the identity (`IsLocalDiffeomorph.exists_diffeomorph_extend_of_isCompact`,
  `Diffeomorph.exists_extend_of_isCompact`,
  `Geometry/Manifold/Diffeomorph/Extend.lean`) and its version for one
  open set at all times (`Diffeotopy.exists_extend_of_isCompact`,
  `Geometry/Diffeomorphism/Diffeotopy/Extend.lean`); the library's
  `TauCeti.Diffeotopy.ofContMDiff` (`Diffeotopy/OfContMDiff.lean`).
- **Forms.** Closed one-forms on a simply connected manifold are exact
  (`TauCeti.exists_mextDeriv_eq_of_simplyConnectedSpace`,
  `Geometry/Manifold/DeRham/SimplyConnected.lean`), and the sphere of
  dimension at least two is simply connected
  (`simplyConnectedSpace_sphere_euclideanSpace`); the relative Poincaré
  operator of a vector bundle, `TauCeti.vectorBundlePoincareHomotopy`
  (`Geometry/Manifold/DifferentialForm/Relative/Basic.lean`).

Neither library has a Dehn twist of a symplectic manifold, Whitney's
theorem on even functions (Tau Ceti's `ContDiff.comp_norm`,
`Analysis/InnerProductSpace/NormPow.lean`, needs the function to vanish
near `0`), the uniqueness of Lagrangian neighbourhoods up to isotopy
(Tau Ceti's `zeroSectionRescale`, `Topology/Homotopy/Isotopy/Linearization.lean`,
is its topological rescaling step for product bundles), or the smoothing
of a continuous path in `TauCeti.Diff`. The part adds, in order of
dependence:

1. Whitney's theorem for smooth even and odd functions;
2. the rescaled family of a symplectic embedding near the zero section,
   and the uniqueness of Lagrangian neighbourhoods up to symplectic isotopy;
3. the transplant of a compactly supported diffeomorphism along a smooth
   family of open embeddings, as a diffeotopy;
4. Euclidean coordinates on `T*Sⁿ` and the normalized geodesic flow;
5. the model twist;
6. framings;
7. the twist along a framed Lagrangian sphere, and the milestone.

## Decisions

`DESIGN.md` leaves three questions to this file.

- **How $T$ is built.** $T$ is Tau Ceti's cotangent bundle `T*Sⁿ` itself,
  not a submanifold of $\mathbb R^{n+1}\times\mathbb R^{n+1}$. The
  Lagrangian neighbourhood theorem produces maps out of `T*Sⁿ`, and cotangent
  lifts and the Liouville form are already there; the submanifold would need
  a symplectomorphism to `T*Sⁿ` before it could be used. The page's
  coordinates come from a map `cotangentCoord : T*Sⁿ → E × E`,
  $z\mapsto(q,p)$, where $p\in q^\perp$ is the vector with
  $\langle p,d\iota\,v\rangle=z(v)$ for the inclusion $\iota$ of the
  sphere, and from its inverse on the image, `cotangentMk q p`. Both are
  smooth, `cotangentCoord` is injective with image
  $\{|q|=1,\ \langle q,p\rangle=0\}$, and it pulls $\sum_jp_j\,dq_j$ back
  to `λ`. So the page's $\lambda_{\mathrm{can}}$ is `λ`, and its
  $\omega_{\mathrm{can}}=d\lambda_{\mathrm{can}}$ is
  `-CotangentBundle.symplecticForm`. Every formula of the page is a
  theorem about `cotangentCoord`, and the definitions use `cotangentMk`.
- **Signs.** The page writes Hamiltonian vector fields with
  $\iota(X_H)\omega=-dH$ and $\omega_{\mathrm{can}}=d\lambda$, Tau Ceti with
  $\iota(X_H)\sigma=dH$ and $\sigma=-d\lambda$. The two sign changes cancel:
  the page's $X_H$ on $(T,\omega_{\mathrm{can}})$ is Tau Ceti's
  `hamiltonianVectorField` of `H` for `CotangentBundle.symplecticForm`, and
  the statements use that. A map preserves $\omega_{\mathrm{can}}$ exactly
  when it preserves `symplecticForm`. Only the embedding $\iota$ of the
  milestone sees the sign: it pulls `ω` back to
  `-CotangentBundle.symplecticForm`. Tau Ceti's theorem gives $\psi$ with
  $\psi^*\omega=$ `symplecticForm`, and $\iota=\psi\circ N$ for the fibrewise
  negation $N=m_{-1}$, Tau Ceti's `vectorBundleScalarDiffeomorph` by $-1$,
  as the page says.
- **The isotopy relation of framings.** $f_1\sim f_2$ when
  $f_1=f_2\circ\Phi_1\circ g$ for a smooth isotopy `Φ : TauCeti.Diffeotopy
  (𝓡 n) ∞ Sⁿ` and some $g\in O(n+1)$, acting by `orthogonalToDiffSphere`.
  This is $f_2^{-1}\circ f_1$ isotopic to $g$, read with smooth isotopies,
  as in Hirsch's *Differential Topology*, Chapter 8. The proof needs a smooth
  isotopy: it extends the isotopy $f_2\circ\Phi_t$ of Lagrangian embeddings
  to a symplectic isotopy of a neighbourhood. A smooth isotopy gives a path
  in the weak Whitney topology (`TauCeti.Diffeotopy.toPath`,
  `Diffeotopy/Path.lean`), so each class of the path reading is a union of
  classes here. The two readings agree once continuous paths in
  `TauCeti.Diff` can be smoothed, which neither library proves. The theorem
  for the path reading would then follow from the one here with no further
  work on twists.
- **Uniqueness of Lagrangian neighbourhoods.** The page's route needs it
  for the zero section of `T*Sⁿ` only, and the proof works for every `T*L`.
  Let $U\subseteq T^*L$ be open and contain the zero section, and let
  $\psi\colon U\to T^*L$ be an open symplectic embedding that fixes every
  zero covector. With the dilations $m_c$
  of *What exists*, $m_c^*\lambda=c\lambda$ for $c\ne0$.
  Then $\psi_t:=m_{1/t}\circ\psi\circ m_t$ is symplectic for $t\in(0,1]$,
  and it is defined on every fibrewise star-shaped $U'\subseteq U$. In a
  bundle chart, $\psi(x,p)=(a(x,p),b(x,p))$ with $a(x,0)=x$ and $b(x,0)=0$,
  so $\psi_t(x,p)=(a(x,tp),\int_0^1\partial_pb(x,stp)\,p\,ds)$, which is
  smooth on $[0,1]\times U'$. At $t=0$ it is the fibrewise linear map
  $\partial_pb(x,0)$. A symplectic map that fixes the zero section has the
  identity there: the zero section is Lagrangian and fixed, so
  $d\psi(v,0)=(v,0)$, and $\omega((v,0),d\psi(0,b))=b(v)$ forces the
  vertical block to be the identity. So $\psi_t$ is a symplectic isotopy
  from the inclusion to $\psi$ that fixes the zero section, and two
  symplectic embeddings $\iota_0,\iota_1$ into `M` that agree on the zero
  section are joined by $\iota_1\circ\psi_t$, with
  $\psi=\iota_1^{-1}\circ\iota_0$ near the zero section. This is the
  statement of [Seidel1997Thesis], Lemma 2.2(b), for every $n$, by the
  rescaling argument of the uniqueness of tubular neighbourhoods (Hirsch,
  *Differential Topology*, Chapter 4, §5).

Two readings of the statement complete these.

- **The domain of $\iota$.** The page embeds the closed $T(r)$ and takes a
  model twist supported in its interior. Here $\iota$ is a diffeomorphism
  `ι : U ≃ₘ⟮_, I⟯ V` between open sets `U : Opens T*Sⁿ` and `V : Opens M`,
  the form of the Lagrangian neighbourhood theorem, and the model twist has
  support in $T(r_0)\subseteq U$. A symplectic embedding of $T(r)$ restricts
  to one of its interior, which contains $T(r_0)$ for $r_0<r$, so this
  covers the page's choices. A manifold with boundary is replaced by its
  interior, so `M` has no boundary.
- **Isotopy classes with compact support.** Two compactly supported
  symplectomorphisms are isotopic when $\tau_2=\Phi_1\circ\tau_1$ for a
  diffeotopy $\Phi$ of `M` whose slices preserve `ω` and which is the
  identity outside one compact set. This is a smooth path in the group of
  compactly supported symplectomorphisms, so it implies the reading by
  continuous paths.

## Files and declarations

Sizes are estimates.

### `Analysis/Calculus/ContDiff/Even.lean`

Whitney's theorem, for real functions of a real variable.

```lean
theorem Function.Even.exists_contDiff_comp_sq {f : ℝ → ℝ} (hf : f.Even)
    (hc : ContDiff ℝ ∞ f) : ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ ∀ t, f t = g (t ^ 2)
theorem Function.Odd.exists_contDiff_mul_comp_sq {f : ℝ → ℝ} (hf : f.Odd)
    (hc : ContDiff ℝ ∞ f) : ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ ∀ t, f t = t * g (t ^ 2)
theorem Function.Even.contDiff_comp_norm {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {f : ℝ → ℝ} (hf : f.Even) (hc : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun v : V ↦ f ‖v‖
```

The odd case is Hadamard's lemma: $f(t)=t\int_0^1f'(st)\,ds$, and the
integral is smooth and even. For the even case, $D\colon f\mapsto f'(t)/t$
maps smooth even functions to smooth even functions, by the odd case
applied to $f'$. So $g(s)=f(\sqrt s)$ has the derivatives
$g^{(k)}(s)=2^{-k}(D^kf)(\sqrt s)$ on $(0,\infty)$, which extend
continuously to $0$. Hence $g$ is smooth on $[0,\infty)$, and the library's
Seeley extension (`Analysis/Calculus/ContDiff/Seeley/Extension.lean`)
extends it to $\mathbb R$. The third theorem is the first composed with
`contDiff_norm_sq`. Expected size: 250 lines.

### `Geometry/Symplectic/Cotangent/Bundle/Rescaling.lean`

For a manifold `L` modelled on `J`, write `T*L := TauCeti.CotangentBundle J L`.
The dilations $m_c$ and the family $(z,t)\mapsto m_tz$ are Tau Ceti's
(*What exists*); the file adds the rescaled family of an embedding and the
uniqueness theorems.

```lean
-- in `Geometry/Manifold/VectorBundle/RescaledFamily.lean`, for any real vector bundle `V`:
/-- For `t > 0`, `m_{1/t} ∘ ψ ∘ m_t`; for `t = 0`, the fibre derivative of `ψ` along the
zero section. -/
def vectorBundleRescaledFamily {U : Opens (TotalSpace F V)} (ψ : U → TotalSpace F V)
    (p : TotalSpace F V × Icc (0 : ℝ) 1) : TotalSpace F V
theorem vectorBundleRescaledFamily_of_pos (ψ) {t : Icc (0 : ℝ) 1} (ht : 0 < (t : ℝ))
    (z : TotalSpace F V) (hz : vectorBundleFiberScaling _ _ (z, t) ∈ U) :
    vectorBundleRescaledFamily ψ (z, t) = m_{1/t} (ψ ⟨vectorBundleFiberScaling _ _ (z, t), hz⟩)
theorem contMDiffOn_vectorBundleRescaledFamily [IB.Boundaryless] [CompleteSpace F] [T2Space B]
    {U' : Set (TotalSpace F V)} (hstar : ∀ z ∈ U', ∀ t, vectorBundleFiberScaling _ _ (z, t) ∈ U)
    (hψ : ContMDiff _ _ ∞ ψ) (hψ0 : ∀ x (hx : 0_x ∈ U), ψ ⟨0_x, hx⟩ = 0_x) :
    ContMDiffOn _ _ ∞ (vectorBundleRescaledFamily ψ) (U' ×ˢ univ)

theorem CotangentBundle.exists_smoothIsotopy_of_eqOn_zeroSection
    [CompactSpace L] {U : Opens T*L} (hU : range (zeroSection …) ⊆ U)
    (ψ : C^∞⟮_, U; _, T*L⟯) (hψ : IsOpenEmbedding ψ)
    (hψ0 : ∀ x, ψ ⟨0_x, _⟩ = 0_x)
    (hψω : mpullback ψ (symplecticForm J L) = mpullback Subtype.val (symplecticForm J L)) :
    ∃ (U' : Opens T*L) (hU' : U' ≤ U) (hzero : range (zeroSection …) ⊆ U')
      (F : SmoothIsotopy (inclusion of U') (ψ ∘ inclusion U' U)),
      F.IsSymplectic (symplecticForm restricted to U') (symplecticForm J L) ∧
      (∀ t x, F (t, ⟨0_x, _⟩) = 0_x) ∧ ∀ t, IsOpenEmbedding (F (t, ·))
```

The isotopy is `vectorBundleRescaledFamily ψ`, the family $m_{1/t}\circ\psi\circ m_t$
of *Decisions*, on a star-shaped neighbourhood $U'$, which exists because
`L` is compact. Its smoothness at $t=0$ is Hadamard's lemma in the fibre
variable, in the trivializations of `T*L`. Those are linear on fibres, so
they commute with $m_t$. The first jet along the zero section gives the
value at $t=0$, as *Decisions* says. For $t>0$ each slice is symplectic by
`mpullback_vectorBundleScalarDiffeomorph_symplecticForm`. Each slice is an
open embedding, being a composite of open embeddings for $t>0$ and the inclusion for
$t=0$.

```lean
theorem IsLagrangianMap.exists_smoothIsotopy_of_apply_zeroSection_eq
    [CompactSpace L] {U₀ U₁ : Opens T*L} {V₀ V₁ : Opens M}
    (ι₀ : U₀ ≃ₘ⟮_, I⟯ V₀) (ι₁ : U₁ ≃ₘ⟮_, I⟯ V₁)
    (h₀ : ι₀^* ω = (symplecticForm J L)|U₀) (h₁ : ι₁^* ω = (symplecticForm J L)|U₁)
    (h : ∀ x, ι₀ ⟨0_x, _⟩ = ι₁ ⟨0_x, _⟩) :
    ∃ (U : Opens T*L) (hU : U ≤ U₀ ⊓ U₁) (hzero : range (zeroSection …) ⊆ U)
      (G : SmoothIsotopy (ι₀ ∘ inclusion) (ι₁ ∘ inclusion)),
      G.IsSymplectic (symplecticForm J L)|U ω ∧ (∀ t x, G (t, ⟨0_x, _⟩) = ι₀ ⟨0_x, _⟩) ∧
      ∀ t, IsOpenEmbedding (G (t, ·))
```

This is the uniqueness of Lagrangian neighbourhoods up to isotopy, with
$G_t=\iota_1\circ\psi_t$ for $\psi=\iota_1^{-1}\circ\iota_0$ on a
neighbourhood of the zero section that $\iota_0$ maps into $V_1$. The same
statement holds with `-symplecticForm`, by composing with $N=m_{-1}$.
That is the form used for the twist (*Decisions*, signs). Expected size: 500
lines, as two issues: the rescaled family and its smoothness (300), and the
two isotopy theorems (200).

### `Geometry/Diffeomorphism/Diffeotopy/Extend.lean`

Named like Tau Ceti's file. It moves a compactly supported diffeomorphism
along a smooth family of open embeddings.

```lean
theorem TauCeti.SmoothIsotopy.exists_diffeotopy_comp_eq_extend
    [T2Space M] {W : Type*} … {g₀ g₁ : C^∞⟮I', W; I, M⟯} (G : SmoothIsotopy g₀ g₁)
    (hGd : ∀ t, IsLocalDiffeomorph I' I ∞ (G (t, ·)))
    (Λ : W ≃ₘ⟮I', I'⟯ W) {K : Set W} (hK : IsCompact K) (hΛ : ∀ w ∉ K, Λ w = w) :
    ∃ (Λ₀ : M ≃ₘ⟮I, I⟯ M) (Φ : Diffeotopy I ∞ M),
      (∀ t w, Φ.timeSlice t (Λ₀ (G (t, w))) = G (t, Λ w)) ∧
      (∀ t x, x ∉ (fun p ↦ G p) '' (univ ×ˢ K) → Φ (t, x) = x) ∧
      (∀ w, Λ₀ (g₀ w) = g₀ (Λ w)) ∧ ∀ x ∉ g₀ '' K, Λ₀ x = x
```

`Λ₀` is the transplant of `Λ` along $g_0$, and $\Phi_t\circ\Lambda_0$ the
transplant along $G_t$. The proof applies
`IsLocalDiffeomorph.exists_diffeomorph_extend_of_isCompact` once, on the
manifold `unitInterval × M`, to the open embedding $(t,w)\mapsto(t,G_t w)$
and the diffeomorphism $(t,w)\mapsto(t,\Lambda w)$. The result preserves
the time coordinate, and composing it with $\mathrm{id}\times\Lambda_0^{-1}$ makes
$\Phi_t=\Lambda_t\circ\Lambda_0^{-1}$ a diffeotopy. If Tau Ceti's theorem
needs a model without boundary, the same is done on `ℝ × M` after
extending `G` past both ends of the interval, as *Manifolds, families and
signs* of `DESIGN.md` describes. A second theorem,
`TauCeti.SmoothIsotopy.exists_diffeotopy_comp_eq_extend_of_isSymplectic`,
adds forms: if `G` is symplectic from `τ` on `W` to `σ` on `M` and `Λ`
preserves `τ`, then $\Lambda_0$ and every $\Phi_t$ preserve `σ`. This is
checked on the image of $G_t$ and on the complement of the compact image of
`K`, two open sets that cover `M`. Expected size: 300 lines.

### `Geometry/Symplectic/DehnTwist/Geodesic.lean`

Coordinates on `T*Sⁿ` and the normalized geodesic flow.

```lean
def cotangentMk (q : Sⁿ) (p : E) : T*Sⁿ        -- the covector v ↦ ⟪p, dι v⟫ at q
def cotangentCoord (z : T*Sⁿ) : E × E          -- (q, p), p ∈ (ℝ ∙ q)ᗮ
def cotangentNorm (z : T*Sⁿ) : ℝ               -- μ z = ‖(cotangentCoord z).2‖
theorem cotangentNorm_eq_norm (z : T*Sⁿ) : cotangentNorm z = ‖z.snd‖   -- round metric
theorem isCompact_setOf_cotangentNorm_le (r : ℝ) : IsCompact {z : T*Sⁿ | cotangentNorm z ≤ r}
theorem cotangentCoord_cotangentMk (q : Sⁿ) (p : E) :
    cotangentCoord (cotangentMk q p) = ((q : E), p - ⟪(q : E), p⟫ • q)
theorem cotangentMk_cotangentCoord (z : T*Sⁿ) : cotangentMk z.proj (cotangentCoord z).2 = z
theorem range_cotangentCoord : range cotangentCoord = {x | ‖x.1‖ = 1 ∧ ⟪x.1, x.2⟫ = 0}
theorem contMDiff_cotangentMk : ContMDiff ((𝓡 n).prod 𝓘(ℝ, E)) _ ∞ (fun x ↦ cotangentMk x.1 x.2)
theorem contMDiff_cotangentCoord : ContMDiff _ 𝓘(ℝ, E × E) ∞ cotangentCoord
theorem mpullback_cotangentCoord :     -- cotangentLiouvilleForm is Σⱼ pⱼ dqⱼ on E × E*
    mpullback _ _ (cotangentInnerEquiv ∘ cotangentCoord) cotangentLiouvilleForm =
      (liouvilleForm (𝓡 n) Sⁿ).val
theorem cotangentCoord_cotangent_orthogonal (A : O(n+1)) (z : T*Sⁿ) :
    cotangentCoord ((orthogonalToDiffSphere n ∞ A).cotangent z) =
      (UnitaryGroup.toLinearIsometryEquiv A q, UnitaryGroup.toLinearIsometryEquiv A p)

def antipodal : T*Sⁿ ≃ₘ⟮_, _⟯ T*Sⁿ             -- the cotangent lift of -1 ∈ O(n+1)
theorem cotangentCoord_antipodal (z) : cotangentCoord (antipodal z) = -cotangentCoord z
def geodesicFlow (t : ℝ) (z : T*Sⁿ) : T*Sⁿ     -- the page's σ_t off the zero section, z on it
theorem cotangentCoord_geodesicFlow {z} (hz : cotangentNorm z ≠ 0) (t : ℝ) :
    cotangentCoord (geodesicFlow t z) =
      (cos t • q + (sin t / ‖p‖) • p, cos t • p - (sin t * ‖p‖) • q)
theorem geodesicFlow_add, geodesicFlow_zero, geodesicFlow_two_pi,
  cotangentNorm_geodesicFlow, geodesicFlow_pi (hz) : geodesicFlow π z = antipodal z
theorem not_exists_continuous_eqOn_geodesicFlow {t : ℝ} (ht₀ : 0 < t) (ht : t < π) :
    ¬ ∃ g : T*Sⁿ → T*Sⁿ, Continuous g ∧ ∀ z, cotangentNorm z ≠ 0 → g z = geodesicFlow t z
theorem isMIntegralCurve_geodesicFlow {z} (hz : cotangentNorm z ≠ 0) :
    IsMIntegralCurve (geodesicFlow · z)
      fun w ↦ (symplecticForm (𝓡 n) Sⁿ).hamiltonianVectorField cotangentNorm w
```

`cotangentMk` is built with `TauCeti.CotangentBundle.contMDiff_mk_comp_mfderiv`,
and the inverse of `cotangentCoord` on its image with
`TauCeti.sphereTangentEquiv`. `mpullback_cotangentCoord` is the chain rule
for the inclusion composed with the bundle projection. In `cotangentNorm_eq_norm`
the norm on covectors is that of Tau Ceti's round metric, the global instance
`TauCeti.instRiemannianBundleSphere`. Write $T(r)$ for
`{z | cotangentNorm z ≤ r}`. It is closed and lies in the image of
`codiscBundle` under $m_{\max(r,1)}$ (`vectorBundleScalarDiffeomorph`),
hence is compact by `isCompact_codiscBundle`. The great circle through
`q` in the direction `p/‖p‖` is Tau Ceti's `sphereGreatCircle`, whose
period and antipode give `geodesicFlow_two_pi` and `geodesicFlow_pi`. The
flow statement is a computation in coordinates: the velocity of the curve is
the vector $(p/|p|,-|p|q)$ at the base point $(q,p)$, and contracting it
with $-d\lambda$ gives $d\mu$, computed with `mpullback_cotangentCoord`. The
restriction to $\mu\ne0$ is needed because $\mu$ is not differentiable on
the zero section. For $0<t<\pi$, the limits of $\sigma_t(q,\pm sp)$ as
$s\to0^+$ have the base points $\cos t\,q\pm\sin t\,u$, which differ, so no
continuous extension exists. This uses $n\ge1$, so that a unit
$u\perp q$ exists. For $n=0$ the theorem is stated with `[NeZero n]`.
Expected size: 600 lines, as two issues: the coordinates and `antipodal`
(300), and the geodesic flow (300).

### `Geometry/Symplectic/DehnTwist/Model.lean`

The model twist.

```lean
/-- `R` is a profile of a model twist with support radius `r₀`. -/
def IsTwistProfile (R : ℝ → ℝ) (r₀ : ℝ) : Prop :=
  ContDiff ℝ ∞ R ∧ (∀ t, R (-t) = R t - t) ∧ ∀ t, r₀ ≤ t → R t = 0
theorem isTwistProfile_iff, IsTwistProfile.deriv_zero (hR) : deriv R 0 = 1 / 2,
  IsTwistProfile.pos (hR) : 0 < r₀,          -- R' (0) = 1/2 rules out r₀ ≤ 0
  IsTwistProfile.deriv_eq_zero (hR) (ht : r₀ ≤ t) : deriv R t = 0,
  IsTwistProfile.lineMap (h₀ : IsTwistProfile R₀ r₀) (h₁ : IsTwistProfile R₁ r₀) (s : ℝ) :
    IsTwistProfile (fun t ↦ (1 - s) * R₀ t + s * R₁ t) r₀,
  exists_isTwistProfile (hr : 0 < r₀) : ∃ R, IsTwistProfile R r₀

def modelTwistFun (R : ℝ → ℝ) (z : T*Sⁿ) : T*Sⁿ :=
  if cotangentNorm z = 0 then antipodal z else geodesicFlow (2 * π * deriv R (cotangentNorm z)) z
def modelTwist (hR : IsTwistProfile R r₀) : T*Sⁿ ≃ₘ⟮_, _⟯ T*Sⁿ
theorem coe_modelTwist (hR) : ⇑(modelTwist hR) = modelTwistFun R
theorem modelTwist_apply_of_le (hR) {z} (hz : r₀ ≤ cotangentNorm z) : modelTwist hR z = z
theorem modelTwist_cotangent_orthogonal (hR) (A : O(n+1)) (z) :
    modelTwist hR ((orthogonalToDiffSphere n ∞ A).cotangent z) =
      (orthogonalToDiffSphere n ∞ A).cotangent (modelTwist hR z)
def twistPrimitive (R : ℝ → ℝ) (z : T*Sⁿ) : ℝ :=
  2 * π * (deriv R (cotangentNorm z) * cotangentNorm z - R (cotangentNorm z))
theorem contMDiff_twistPrimitive (hR) : ContMDiff _ 𝓘(ℝ) ∞ (twistPrimitive R)
theorem mpullback_modelTwist_liouvilleForm (hR) :
    mpullback (modelTwist hR) _ (liouvilleForm (𝓡 n) Sⁿ) =
      liouvilleForm (𝓡 n) Sⁿ + mextDerivₗ (twistPrimitive R)
theorem mpullback_modelTwist_symplecticForm (hR) :
    mpullback (modelTwist hR) _ (symplecticForm (𝓡 n) Sⁿ) = symplecticForm (𝓡 n) Sⁿ
theorem isMIntegralCurve_geodesicFlow_twistProfile (hR) {z} (hz : cotangentNorm z ≠ 0) :
    -- t ↦ geodesicFlow (t * deriv R (μ z)) z is an integral curve of X_{R ∘ μ} on μ ≠ 0,
    -- and its value at 2π is modelTwist hR z
theorem exists_isCompactlySupportedHamiltonian_modelTwist
    (h₀ : IsTwistProfile R₀ r₀) (h₁ : IsTwistProfile R₁ r₀) :
    ∃ Φ : Diffeotopy _ ∞ T*Sⁿ, Φ.IsCompactlySupportedHamiltonian (symplecticForm (𝓡 n) Sⁿ) ∧
      (∀ t z, r₀ ≤ cotangentNorm z → Φ (t, z) = z) ∧ ∀ z, Φ.final (modelTwist h₀ z) = modelTwist h₁ z
```

**Smoothness across the zero section.** Write $\theta=2\pi R'$. From
$R(-t)=R(t)-t$, $R'(t)+R'(-t)=1$, so $\cos\theta$ is even and $\sin\theta$
is odd. By Whitney's theorem, $\cos\theta(t)=C(t^2)$ and
$\sin\theta(t)=t\,S(t^2)$ with $C,S$ smooth, and
$$
\mathrm{coord}(\tau z)=\big(C(|p|^2)\,q+S(|p|^2)\,p,\ C(|p|^2)\,p-|p|^2S(|p|^2)\,q\big),
$$
a smooth map of $(q,p)$ that agrees with `modelTwistFun R` also on the zero
section, where $C(0)=-1$. So `modelTwistFun R` is `cotangentMk` composed
with a smooth map, hence smooth. Since $\sigma_t$ preserves $\mu$, the
inverse is $z\mapsto\sigma_{-\theta(\mu z)}z$, smooth by the same
argument, as $\cos(-\theta)$ is even and $\sin(-\theta)$ odd.
The support, $O(n+1)$-equivariance and `twistPrimitive` (the function
$R'(t)t-R(t)$ is even, so Whitney applies) follow from the coordinates.

**Exactness and symplecticity.** On $\mu\ne0$, the pullback of $\lambda$ by
$z\mapsto\sigma_{\theta(\mu z)}z$ is $\lambda+\mu\,d(\theta\circ\mu)$, by
`mpullback_liouvilleForm_apply_of_proj_comp_eq` and the coordinate
formulas. With $\theta=2\pi R'$ this is $\lambda+dK$ for
$K=$ `twistPrimitive R`. Both sides are smooth forms on `T*Sⁿ`, and the
complement of the zero section is dense for $n\ge1$, so they agree
everywhere. For $n=0$ the zero section is open, the bundle has rank $0$,
$\lambda=0$, and `modelTwistFun R` is the antipodal map of $S^0$. Symplecticity
follows by $d$, as $d\,dK=0$; no separate computation is needed.

**Hamiltonian descriptions.** `isMIntegralCurve_geodesicFlow_twistProfile`
reparametrizes `isMIntegralCurve_geodesicFlow`, with
`TauCeti.SmoothTwoForm.hamiltonianVectorField_comp`. For the isotopy
between two profiles, $R_s=(1-s)R_0+sR_1$ is a profile for every $s$
(`IsTwistProfile.lineMap`). The function $G=2\pi(R_1-R_0)\circ\mu$ is
smooth, as $R_1-R_0$ is even, and it vanishes for $\mu\ge r_0$.
`exists_isCompactlySupportedHamiltonian` gives $\Phi$ generated by $G$
(constant in time), the identity off $T(r_0)$, which is compact
(`isCompact_setOf_cotangentNorm_le`).
Both $s\mapsto\Phi_s(\tau_{R_0}z)$ and $s\mapsto\tau_{R_s}z$ are integral
curves of $X_G$ through $\tau_{R_0}z$. Off the zero section this is the flow
statement. On it both curves are constant, since $dG=0$ there. So
uniqueness of integral curves gives $\Phi_1\circ\tau_{R_0}=\tau_{R_1}$.
Expected size: 700 lines, as two issues: profiles, the definition,
smoothness, support and equivariance (350); the primitive, symplecticity
and the two Hamiltonian statements (350).

### `Geometry/Symplectic/DehnTwist/Framing.lean`

```lean
/-- Two parametrizations `f₁ f₂ : Sⁿ → M` define the same framing: `f₁ = f₂ ∘ Φ₁ ∘ A`
for a smooth isotopy `Φ` of `Sⁿ` and `A ∈ O(n+1)`. -/
def FramingRel (f₁ f₂ : SmoothEmbedding (𝓡 n) I ∞ Sⁿ M) : Prop :=
  ∃ (Φ : TauCeti.Diffeotopy (𝓡 n) ∞ Sⁿ) (A : Matrix.orthogonalGroup (Fin (n + 1)) ℝ),
    ∀ q, f₁ q = f₂ (Φ.final (orthogonalToDiffSphere n ∞ A q))
theorem framingRel_iff, FramingRel.range_eq, framingRel_equivalence :
  Equivalence (FramingRel (I := I) (M := M) (n := n)),
  framingRel_comp_orthogonal (f) (A) :
    FramingRel (f.compDiffeomorph (orthogonalToDiffSphere n ∞ A)) f,
  framingRel_comp_final (f) (Φ) : FramingRel (f.compDiffeomorph Φ.final) f
def framingSetoid : Setoid (SmoothEmbedding (𝓡 n) I ∞ Sⁿ M)
/-- A framed sphere: a parametrized sphere up to `FramingRel`. -/
def FramedSphere := Quotient (framingSetoid (n := n) (I := I) (M := M))
```

Transitivity uses that $O(n+1)$ normalizes the isotopies: $\Phi_1\circ
A\circ\Psi_1\circ B=\Phi_1\circ(A\Psi_1A^{-1})\circ AB$, and conjugation of
a diffeotopy by a diffeomorphism is a diffeotopy (Tau Ceti's
`Diffeotopy.transDiffeomorph`, with `final_transDiffeomorph_eq_mul_mul_inv`,
and `Diffeotopy.trans` and `symm`). The framing of a Lagrangian sphere `L` is a class of
parametrizations with range `L`; `FramingRel.range_eq` says the range is an
invariant of the class. Expected size: 200 lines.

### `Geometry/Symplectic/DehnTwist/Sphere.lean`

The twist along a framed Lagrangian sphere.

```lean
/-- The Dehn twist built from a symplectic embedding `ι` of a neighbourhood `U` of the
zero section and a model twist supported in `U`: `ι ∘ τ ∘ ι⁻¹` on `V`, the identity off it. -/
def dehnTwist {U : Opens T*Sⁿ} {V : Opens M} (ι : U ≃ₘ⟮_, I⟯ V) (hR : IsTwistProfile R r₀)
    (hU : {z | cotangentNorm z ≤ r₀} ⊆ U) : M ≃ₘ⟮I, I⟯ M
theorem dehnTwist_apply_val (z : U) : dehnTwist ι hR hU (ι z) = ι ⟨modelTwist hR z, _⟩
theorem dehnTwist_apply_of_notMem {x} (hx : x ∉ ι '' {z | cotangentNorm z ≤ r₀}) :
    dehnTwist ι hR hU x = x
theorem isCompact_image_setOf_cotangentNorm_le : IsCompact (ι '' {z | cotangentNorm z ≤ r₀})
theorem mpullback_dehnTwist (hι : ι^* ω = (-symplecticForm)|U) : (dehnTwist ι hR hU)^* ω = ω
theorem dehnTwist_apply_embedding (hιf : ∀ q, ι ⟨0_q, _⟩ = f q) (q : Sⁿ) :
    dehnTwist ι hR hU (f q) = f (-q)
theorem exists_symplecticEmbedding (hf : hω.isNondegenerate.IsLagrangianMap (𝓡 n) f) :
    ∃ (U : Opens T*Sⁿ) (V : Opens M) (ι : U ≃ₘ⟮_, I⟯ V),
      ι^* ω = (-symplecticForm)|U ∧ ∀ q, ∃ h : 0_q ∈ U, ι ⟨0_q, h⟩ = f q
theorem exists_diffeotopy_dehnTwist_eq (hf₁ : IsLagrangianMap f₁) (hf : FramingRel f₁ f₂)
    (hι₁ : ι₁^* ω = …) (hι₁f : ∀ q, ι₁ ⟨0_q, _⟩ = f₁ q) (hR₁ : IsTwistProfile R₁ r₁) (hU₁)
    (hι₂ : ι₂^* ω = …) (hι₂f : ∀ q, ι₂ ⟨0_q, _⟩ = f₂ q) (hR₂ : IsTwistProfile R₂ r₂) (hU₂) :
    ∃ (Φ : Diffeotopy I ∞ M) (K : Set M), IsCompact K ∧
      (∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer ω) ∧ (∀ t x, x ∉ K → Φ (t, x) = x) ∧
      ∀ x, Φ.final (dehnTwist ι₁ hR₁ hU₁ x) = dehnTwist ι₂ hR₂ hU₂ x
theorem exists_mpullback_dehnTwist_sub_eq (θ : SmoothForm I M ℝ 1) (hθ : mextDeriv θ = ω)
    (hθL : ∃ h : C^∞⟮𝓡 n, Sⁿ; ℝ⟯, mpullback f θ = mextDerivₗ h) (hιf : …) (hι : …) :
    ∃ K : C^∞⟮I, M; ℝ⟯, (∀ x ∉ ι '' {z | cotangentNorm z ≤ r₀}, K x = 0) ∧
      mpullback (dehnTwist ι hR hU) θ - θ = mextDerivₗ K
theorem exists_mpullback_dehnTwist_sub_eq_of_two_le (hn : 2 ≤ n) … -- without hθL
```

`dehnTwist` takes the diffeomorphism given by
`IsLocalDiffeomorph.exists_diffeomorph_extend_of_isCompact` for the open
embedding `ι` and the compact set $T(r_0)$
(`isCompact_setOf_cotangentNorm_le`). Its two apply lemmas determine it.
`exists_symplecticEmbedding` is the Lagrangian neighbourhood theorem
composed with $N=m_{-1}$. A model twist with $T(r_0)\subseteq U$
exists by `exists_isTwistProfile` and compactness of the zero section.

`exists_diffeotopy_dehnTwist_eq` follows *Decisions*, in three steps:

1. *The same `f`.* Two models in the same `ι` are joined by
   `exists_isCompactlySupportedHamiltonian_modelTwist`. That diffeotopy is
   the identity off $T(r_0)\subseteq U$, so it restricts to `U`, `ι` conjugates
   it to a diffeotopy of `V`, and Tau Ceti's
   `Diffeotopy.exists_extend_of_isCompact` extends that to `M`. Two embeddings `ι₁ ι₂` that extend `f` are joined by
   `IsLagrangianMap.exists_smoothIsotopy_of_apply_zeroSection_eq` on a
   smaller neighbourhood, after shrinking both models. Moving one model
   along that isotopy, `Diffeotopy/Extend.lean` gives the diffeotopy.
2. *$f\circ A$ for $A\in O(n+1)$.* `ι ∘ (orthogonalToDiffSphere n ∞ A).cotangent`
   extends $f\circ A$ and pulls `ω` back to the same form, since cotangent
   lifts preserve `λ`. `modelTwist_cotangent_orthogonal` shows that both
   choices give the same `dehnTwist`, with no isotopy.
3. *$f\circ\Phi_1$.* The isotopy $e_t=f\circ\Phi_t$ of Lagrangian
   embeddings has $e_t^*\omega=0=f^*\omega$, so
   `exists_isSymplectic_extension_of_mpullback_eq` extends it to a
   symplectic isotopy $F_t$ of a neighbourhood of $L$. Then $F_t\circ\iota$,
   on the part of `U` that `ι` maps into that neighbourhood, is a smooth
   family of symplectic open embeddings from $\iota$ to an embedding that
   extends $f\circ\Phi_1$. `Diffeotopy/Extend.lean` moves a model twist
   along it. Each slice $F_t\circ\iota$ is an immersion between manifolds
   of dimension $2n$, hence a local diffeomorphism. The extension theorem
   does not say that the slices of $F$ are injective, but they are on $L$,
   where $F_t\circ f=f\circ\Phi_t$. So the library's
   `exists_isOpen_forall_isSmoothEmbedding_of_injOn`
   (`Geometry/Manifold/SmoothEmbedding/Neighborhood.lean`, of *Isotopy
   extension*) gives a neighbourhood of $L$ on which every slice is an
   embedding.

For $f_1=f_2\circ\Phi_1\circ A$, steps 2 and 3 and step 1 compose; the
composite of the diffeotopies is `Diffeotopy.trans`, and the union of the
compact sets bounds the support.

Exactness follows the page's route. The closed one-form
$\iota^*\theta-\lambda$ on `U` restricts on the zero section to
$f^*\theta$, which is exact. So on a star-shaped $U'\supseteq T(r_0)$ it is
$dh$, by `TauCeti.vectorBundlePoincareHomotopy` or by homotopy invariance
along `vectorBundleFiberScaling`. Then $\tau^*\theta-\theta=d(K+h\circ\tau-h)$ on $V$,
transported by $\iota$. The function vanishes off $\iota(T(r_0))$, so it
extends by $0$ to a smooth function on `M`. For $n\ge2$,
`TauCeti.exists_mextDeriv_eq_of_simplyConnectedSpace` with
`simplyConnectedSpace_sphere_euclideanSpace` gives `hθL`. Expected size:
650 lines, as two issues: the definition, its properties and the existence of
choices (300); the isotopy class and exactness, with the milestone (350).

## Milestones

| Milestone | Theorems | File |
|---|---|---|
| *Dehn twist along a framed Lagrangian sphere* | `dehnTwist_isSymplectic_and_framing_invariant`, from the theorems above | `DehnTwist/Sphere.lean` |

The milestone theorem is the conjunction of the statements of the page, for
$n\ge1$ and with the readings of *Decisions*:

- the model: for a profile `R` with radius `r₀`, `modelTwist` is a
  diffeomorphism with the page's formula (`cotangentCoord_geodesicFlow`,
  `coe_modelTwist`), equal to `antipodal` on the zero section, the identity
  where $\mu\ge r_0$. It preserves `symplecticForm`, commutes with the
  cotangent lifts of $O(n+1)$, and satisfies
  `mpullback_modelTwist_liouvilleForm` with the page's $K$. Off the zero
  section it is the time-$2\pi$ map of $R\circ\mu$, and two models of radius
  `r₀` are joined by a compactly supported Hamiltonian diffeotopy fixing
  $\mu\ge r_0$;
- the geodesic flow: `geodesicFlow` is the Hamiltonian flow of $\mu$ off the
  zero section, of period $2\pi$, equal to `antipodal` at time $\pi$, and
  for $0<t<\pi$ has no continuous extension;
- the twist along a framed sphere: for every Lagrangian embedding `f` and
  every choice of `ι` and `R`, `dehnTwist` preserves `ω`, is the identity
  outside a compact set, and maps `f q` to `f (-q)`. Choices exist
  (`exists_symplecticEmbedding`, `exists_isTwistProfile`), and the class
  under compactly supported symplectic diffeotopies depends only on the
  class of `f` under `FramingRel`;
- exactness: for `ω = dθ` with $\theta|_L$ exact, and for every `θ` when
  $n\ge2$, the twist is exact with a primitive supported in
  $\iota(T(r_0))$.

The statement is the page's, with the domain of $\iota$ an open
neighbourhood of $T(r_0)$, which is more general, and the framing relation
read with smooth isotopies. *Decisions* says why each reading is chosen.
Neither is an error of the page, so `ERRATA.md` gets no entry. The remark
that a Lagrangian 2-sphere has one framing needs Smale's theorem and is not
part of the milestone (`DESIGN.md`, part 55), and neither is the same
remark for $n=1$, which needs that every diffeomorphism of the circle is
isotopic to an element of $O(2)$.

## What the part uses

- *Symplectic neighbourhoods*: `Neighborhood/Lagrangian.lean` (the
  Lagrangian neighbourhood theorem).
- *Isotopy extension*: `IsotopyExtension/Submanifold.lean`,
  `IsotopyExtension/Velocity.lean` (`SmoothIsotopy.IsSymplectic`) and
  `Geometry/Manifold/SmoothEmbedding/Neighborhood.lean`.
- *Hamiltonian flows*: `Flux/CompactSupport.lean` and `Flux/Hamiltonian.lean`.
- *Smooth families*: `Diffeotopy/OfContMDiff.lean` and
  `Analysis/Calculus/ContDiff/Seeley/Extension.lean`.
- Tau Ceti, as listed in *What exists*.

All of these are merged, so the part is at level 0 of the build order, as
`DESIGN.md` says.

## Building issues

In this order; each is blocked by the ones listed. All are sub-issues of
#2381, *Build the part Dehn twists*.

| # | Issue | Files | Blocked by | Size |
|---|---|---|---|---|
| 1 | Whitney's theorem on smooth even functions | `Analysis/Calculus/ContDiff/Even.lean` | — | 250 |
| 2 | The rescaled family of a symplectic embedding near the zero section | `VectorBundle/RescaledFamily.lean` (`vectorBundleRescaledFamily` and its smoothness) | — | 300 |
| 3 | Uniqueness of Lagrangian neighbourhoods up to isotopy | `Cotangent/Bundle/Rescaling.lean` (the two isotopy theorems) | 2 | 200 |
| 4 | Moving a compactly supported diffeomorphism along a family of embeddings | `Diffeotopy/Extend.lean` | — | 300 |
| 5 | Euclidean coordinates on the cotangent bundle of the sphere | `DehnTwist/Geodesic.lean` (coordinates, `antipodal`) | — | 300 |
| 6 | The normalized geodesic flow | `DehnTwist/Geodesic.lean` (flow) | 5 | 300 |
| 7 | The model Dehn twist | `DehnTwist/Model.lean` (profiles, definition, smoothness) | 1, 6 | 350 |
| 8 | Exactness and Hamiltonian isotopies of the model twist | `DehnTwist/Model.lean` (the rest) | 7 | 350 |
| 9 | Framings of a sphere | `DehnTwist/Framing.lean` | — | 200 |
| 10 | The twist along a Lagrangian sphere | `DehnTwist/Sphere.lean` (definition, properties, choices) | 7, 8 | 300 |
| 11 | Independence of the choices and exactness | `DehnTwist/Sphere.lean` (the rest, the milestone) | 3, 4, 8, 9, 10 | 350 |

Issues 1, 2, 4, 5 and 9 can start at once. The milestone is proved in
issue 11.

## References

* [P. Seidel, *A long exact sequence for symplectic Floer cohomology*][Seidel2003],
  Lemma 1.8, equation (1.7), the paragraph before Proposition 1.11 (arXiv
  version 2).
* [P. Seidel, *Floer homology and the symplectic isotopy problem*][Seidel1997Thesis],
  Lemmas 2.1 and 2.2, Proposition 2.3.
* [P. Seidel, *Lectures on four-dimensional Dehn twists*][Seidel2008], §1a.
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Theorem 3.4.13 and p. 270.
* [V. I. Arnold, *Some remarks on symplectic monodromy of Milnor fibrations*][Arnold1995].
* H. Whitney, *Differentiable even functions*, Duke Mathematical Journal 10
  (1943), 159–160.
* M. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33,
  Springer, 1976, Chapter 4, §5 (tubular neighbourhoods) and Chapter 8
  (isotopies).
