/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField.Right
public import TauCeti.Geometry.Manifold.FiberBundle.Associated.Pullback
public import TauCeti.Geometry.Manifold.FiberBundle.Associated.Section
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Submersion
public import TauCeti.Geometry.Manifold.FiberBundle.Principal.FundamentalVectorField
public import TauCeti.Geometry.Manifold.FiberBundle.Pullback.Basic
public import TauCeti.Geometry.Manifold.FiberBundle.Submersion
public import TauCeti.Geometry.Manifold.Submersion.Split
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Basic
import SymplecticGeometry.Geometry.Lie.FundamentalVectorField
import SymplecticGeometry.Topology.FiberBundle.Basic

/-!
# The product `P × F` as the pull-back of `P` to `P ×_G F`

Let `P` be a principal `G`-bundle over `B`, let `G` act on the left on a manifold `F`, and let
`M = P ×_G F` be the associated bundle, with charted total space
`TauCeti.ManifoldTotalSpace F (AssociatedBundle G P F)` and projection `π_M : M → B`. The
pull-back `Q = π_M^* P` is a principal `G`-bundle over `M`, whose fibre over `[x, v]` is the fibre
of `P` through `x`. The map `Φ (x, v) = ([x, v], x)` identifies `P × F` with the total space of `Q`:
the class `[x, v]` and the point `y = x` of its fibre recover `v` as the unique `w` with
`[y, w] = [x, v]`. Under `Φ`, the projection of `Q` becomes the quotient map `q (x, v) = [x, v]`,
and the principal action of `G` on `Q` becomes the diagonal action `(x, v) · g = (x · g, g⁻¹ v)`.
So the derivative of `Φ` carries the fundamental vectors `(x ξ, -X_ξ(v))` of the diagonal action to
those of `Q`, and `q`, being `π_Q ∘ Φ`, is a surjective submersion. Its fibres are the orbits of
the diagonal action, and the kernel of its derivative at `(x, v)` consists of the vectors
`(x ξ, -X_ξ(v))`. Hence a smooth form on `P × F` that is invariant under the diagonal action and
vanishes on those vectors is basic for `q`, and is the pull-back along `q` of exactly one smooth
form on `M`.

## Main definitions and results

* `TauCeti.AssociatedBundle.chartedMk`: the quotient map `q`, between the charted total spaces,
  with `TauCeti.AssociatedBundle.chartedMk_apply`, `TauCeti.AssociatedBundle.chartedMk_homeomorph`
  and `TauCeti.AssociatedBundle.contMDiff_chartedMk`: it is `C^n`, as Tau Ceti's
  `TauCeti.AssociatedBundle.contMDiff_totalSpaceMk_mk` says of the map written out.
* `TauCeti.AssociatedBundle.pullbackProjDiffeomorph`: the `C^n` diffeomorphism `Φ` from
  `ManifoldTotalSpace G P × F` onto the charted total space of `Q`.
* `TauCeti.AssociatedBundle.pullbackProjDiffeomorph_apply` and
  `TauCeti.AssociatedBundle.pullbackProjDiffeomorph_symm_apply`: `Φ` and its inverse on points.
* `TauCeti.AssociatedBundle.proj_pullbackProjDiffeomorph`: `π_Q ∘ Φ = q`, at each point, and
  `TauCeti.AssociatedBundle.projContMDiffMap_comp_pullbackProjDiffeomorph`: the same as an
  equality of maps, with `π_Q` the `C^n` projection.
* `TauCeti.AssociatedBundle.pullbackProjDiffeomorph_smul`: `Φ` is equivariant for the diagonal
  action on the source and the principal action on the target.
* `TauCeti.AssociatedBundle.pullbackProjSection`: the tautological section `m ↦ m` of the
  bundle `Q ×_G F` over `M`, and `TauCeti.AssociatedBundle.contMDiff_pullbackProjSection`:
  it is `C^n`.
* `TauCeti.AssociatedBundle.sectionFunction_pullbackProjSection_eq_iff` and
  `TauCeti.AssociatedBundle.pullbackProjDiffeomorph_symm_snd_eq_iff`: the second coordinate of
  `Φ⁻¹ (m, y)` is the `w` with `[y, w] = m`.
* `TauCeti.AssociatedBundle.mfderiv_pullbackProjDiffeomorph_fundamental`: the derivative of `Φ`
  sends `(x ξ, -X_ξ(v))` to the fundamental vector of `ξ` on `Q` at `Φ (x, v)`.
* `TauCeti.AssociatedBundle.surjective_chartedMk` and
  `TauCeti.AssociatedBundle.isSubmersion_chartedMk`: `q` is a surjective submersion.
* `TauCeti.AssociatedBundle.contMDiff_op_smul_inv_smul`: the diagonal action is `C^n`.
* `TauCeti.AssociatedBundle.contMDiff_chartedMk_left`: for fixed `v`, `x ↦ [x, v]` is
  `C^n`, and `TauCeti.AssociatedBundle.mfderiv_proj_chartedMk_apply`: composed with the
  derivative of the projection of `M`, its derivative is that of the projection of `P`.
* `TauCeti.AssociatedBundle.contMDiff_chartedMk_right`: for fixed `x`, the fibre inclusion
  `v ↦ [x, v]` is `C^n`.
* `TauCeti.AssociatedBundle.chartedMk_op_smul_inv_smul` and
  `TauCeti.AssociatedBundle.chartedMk_eq_chartedMk_iff`: `q` is invariant under the
  diagonal action, and its fibres are the orbits.
* `TauCeti.AssociatedBundle.mfderiv_chartedMk_eq_zero_iff`: the kernel of the derivative
  of `q` at `(x, v)` is made of the vectors `(x ξ, -X_ξ(v))`.
* `TauCeti.AssociatedBundle.isBasic_chartedMk` and
  `TauCeti.AssociatedBundle.existsUnique_mpullback_chartedMk_eq`: a smooth form on `P × F`
  invariant under the diagonal action and vanishing on the vectors `(x ξ, -X_ξ(v))` is basic for
  `q`, and is the pull-back along `q` of a unique smooth form on `M`.

## Implementation notes

The fibre of `Q` over `Φ (x, v)` is that of `P` over the projection of `[x, v]`, which is the base
point of `x` only up to an equation (`TauCeti.ManifoldTotalSpace.homeomorph` does not unfold), so
`Φ` transports `x` along it. The forward map is smooth by the universal property of the pull-back
(`TauCeti.ManifoldTotalSpace.contMDiff_pullback_iff`). The second coordinate of the inverse is the
equivariant function `TauCeti.AssociatedBundle.sectionFunction` of the tautological section, so it
is smooth by `TauCeti.AssociatedBundle.contMDiff_sectionFunction`; the section itself is smooth
since Tau Ceti's comparison `TauCeti.AssociatedBundle.pullbackHomeomorph` of `Q ×_G F` with the
pull-back of `M` to `M` is smooth (`TauCeti.AssociatedBundle.contMDiff_pullbackHomeomorph_iff`).

Tau Ceti's lemmas composing a submersion with a local diffeomorphism need one model on both
sides, and `Φ` changes the model. So the submersion property of `q` is read off its derivative,
which is surjective as that of `π_Q` composed with an isomorphism; Tau Ceti's
`ContMDiff.isSubmersionOfComplement_of_surjective_mfderiv` turns this into a submersion, for
finite-dimensional manifolds without boundary.

The derivative of `Φ` on fundamental vectors comes from the chain rule along the orbit map of the
diagonal action, which `Φ` turns into the orbit map of `Q` (`pullbackProjDiffeomorph_smul`). Its
second component `g ↦ g⁻¹ • v` has derivative `ξ ↦ -X_ξ(v)` at `1`, by
`TauCeti.mfderiv_inv_smul_one_apply`.

The declarations from `pullbackProjSection` to `mfderiv_pullbackProjDiffeomorph_fundamental` take
`[∀ b, Nonempty (P b)]`. Their statements need it, not only their proofs: Mathlib's and Tau
Ceti's fibre bundle structure on the pull-back `Q` asks for it, and so does `pullbackEquiv`. A
caller supplies it with `have := FiberBundle.nonempty_fiber G P`, since `G` is nonempty. The
statements after them do not mention `Q`. Of these, `isSubmersion_chartedMk` and
`mfderiv_chartedMk_eq_zero_iff` derive the hypothesis in their proofs in this way; the
descent theorems reach `Q` only through those two results and need no such step.

The descent does not transport the descent of basic forms on principal bundles along `Φ`: Tau
Ceti's `TauCeti.RoughForm.isBasic_of_mpullback_eq` applies to `q` directly, with the diagonal
action as the family of maps over `q`, and Tau Ceti's smooth descent
`TauCeti.SmoothForm.descendedForm` then gives the form on `M`, unique by
`TauCeti.SmoothForm.eq_descendedForm_iff`. `Φ` enters only through the kernel of the derivative
of `q`. The statement of the descent is about smooth forms on `M`, so it takes the instance
`[ContMDiffFiberBundle ∞ F (AssociatedBundle G P F) IB IF]`, which a caller supplies with
`have := contMDiffFiberBundle IG`; Tau Ceti does not make it an instance, since `IG` does not
appear in its conclusion.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter I, §5 (associated bundles).
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.3.
-/

public section

noncomputable section

open Bundle MulOpposite TauCeti
open scoped Manifold ContDiff

namespace TauCeti.AssociatedBundle

section

variable {n : ℕ∞ω} {𝕜 B G F : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners 𝕜 EG HG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF} [TopologicalSpace F] [ChartedSpace HF F] [MulAction G F]
  [ContinuousSMul G F]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

/-- The projection `π_M` of the associated bundle, as a `C^n` map. -/
local notation "πM" => ManifoldTotalSpace.projContMDiffMap n F (AssociatedBundle G P F) IB IF

/-- The pull-back `Q = π_M^* P` of `P` to the associated bundle. -/
local notation "Q" => (πM : ManifoldTotalSpace F (AssociatedBundle G P F) → B) *ᵖ P

/-! ### The quotient map between charted total spaces -/

variable (G P F) in
/-- The quotient map `q (x, v) = [x, v]` from `P × F` onto the associated bundle `P ×_G F`, between
the charted total spaces: it sends `(x, v)` to the class `AssociatedBundle.mk G p v`, for the point
`p` of the total space of `P` that `x` stands for, read in the charted total space of `P ×_G F`. -/
def chartedMk (x : ManifoldTotalSpace G P × F) : ManifoldTotalSpace F (AssociatedBundle G P F) :=
  ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)
    ⟨((ManifoldTotalSpace.homeomorph G P).symm x.1).proj,
      mk G ((ManifoldTotalSpace.homeomorph G P).symm x.1).snd x.2⟩

/-- The quotient map written out through `TauCeti.ManifoldTotalSpace.homeomorph`. -/
theorem chartedMk_apply (x : ManifoldTotalSpace G P × F) :
    chartedMk G F P x =
      ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)
        ⟨((ManifoldTotalSpace.homeomorph G P).symm x.1).proj,
          mk G ((ManifoldTotalSpace.homeomorph G P).symm x.1).snd x.2⟩ := (rfl)

/-- The quotient map at a point `p` of the total space of `P` is the class `[p, v]`. -/
@[simp]
theorem chartedMk_homeomorph (p : TotalSpace G P) (v : F) :
    chartedMk G F P (ManifoldTotalSpace.homeomorph G P p, v) =
      ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F) ⟨p.proj, mk G p.snd v⟩ := by
  rw [chartedMk_apply, Homeomorph.symm_apply_apply]

/-- Read in the total space of `P ×_G F`, the quotient map sends `(x, v)` to the class of
`(p, v)`, for the point `p` of the total space of `P` that `x` stands for. -/
@[simp]
theorem homeomorph_symm_chartedMk (x : ManifoldTotalSpace G P × F) :
    (ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm (chartedMk G F P x) =
      ⟨((ManifoldTotalSpace.homeomorph G P).symm x.1).proj,
        mk G ((ManifoldTotalSpace.homeomorph G P).symm x.1).snd x.2⟩ := by
  rw [chartedMk_apply, Homeomorph.symm_apply_apply]

variable (n IB IG IF) in
/-- The quotient map `(x, v) ↦ [x, v]` is `C^n`. -/
theorem contMDiff_chartedMk [ContMDiffSMul IG IF n G F] :
    ContMDiff ((IB.prod IG).prod IF) (IB.prod IF) n (chartedMk G F P) :=
  contMDiff_totalSpaceMk_mk n G F IB IG IF P

variable (n IB IF) in
/-- The point `([x, v], x)` of the total space of `Q`, before transport to its charted copy. -/
def pullbackProjMk (x : ManifoldTotalSpace G P × F) : TotalSpace G Q :=
  ⟨chartedMk G F P x,
    cast (congrArg P (by simp)) ((ManifoldTotalSpace.homeomorph G P).symm x.1).snd⟩

variable (n IB IF) in
/-- The projection of `([x, v], x)` is the class `[x, v]`. -/
@[simp]
theorem pullbackProjMk_proj (x : ManifoldTotalSpace G P × F) :
    (pullbackProjMk n IB IF x).proj = chartedMk G F P x := (rfl)

variable (n IB IF) in
/-- The image of `([x, v], x)` in the total space of `P` is `x`. -/
@[simp]
theorem lift_pullbackProjMk (x : ManifoldTotalSpace G P × F) :
    Pullback.lift πM (pullbackProjMk n IB IF x) = (ManifoldTotalSpace.homeomorph G P).symm x.1 := by
  refine (Pullback.lift_mk _ _ _).trans ?_
  exact (TotalSpace.mk_cast (by simp) _).trans (TotalSpace.eta _)

/-- **The quotient map onto the associated bundle is surjective**: every point of `P ×_G F` is a
class `[x, v]`. -/
theorem surjective_chartedMk : Function.Surjective (chartedMk G F P) := by
  intro y
  obtain ⟨⟨p, v⟩, hp⟩ := (isOpenQuotientMap_totalSpaceMk_mk G P F).surjective
    ((ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm y)
  refine ⟨(ManifoldTotalSpace.homeomorph G P p, v), ?_⟩
  rw [chartedMk_homeomorph]
  exact (congrArg _ hp).trans (Homeomorph.apply_symm_apply _ _)

/-- **The quotient map is invariant under the diagonal action**: `[x · g, g⁻¹ • v] = [x, v]`. -/
theorem chartedMk_op_smul_inv_smul (g : G) (x : ManifoldTotalSpace G P × F) :
    chartedMk G F P (op g • x.1, g⁻¹ • x.2) = chartedMk G F P x := by
  rw [chartedMk_apply, chartedMk_apply, ManifoldTotalSpace.homeomorph_symm_smul, mk_smul_inv_smul]

omit [ContinuousSMul G F] in
/-- The diagonal action `(x, v) ↦ (x · g, g⁻¹ • v)` of `g : G` on `P × F` is `C^n`. -/
theorem contMDiff_op_smul_inv_smul [LieGroup IG n G] [ContMDiffSMul IG IF n G F] (g : G) :
    ContMDiff ((IB.prod IG).prod IF) ((IB.prod IG).prod IF) n
      fun x : ManifoldTotalSpace G P × F ↦ (op g • x.1, g⁻¹ • x.2) :=
  ((contMDiff_const_smul (op g)).comp contMDiff_fst).prodMk
    ((ContMDiffSMul.contMDiff_const_smul (I := IG) g⁻¹).comp contMDiff_snd)

variable (n IB IF) in
/-- For a fixed `v : F`, the map `x ↦ [x, v]` from the total space of `P` to that of the associated
bundle is `C^n`. -/
theorem contMDiff_chartedMk_left [ContMDiffSMul IG IF n G F] (v : F) :
    ContMDiff (IB.prod IG) (IB.prod IF) n fun x : ManifoldTotalSpace G P ↦
      chartedMk G F P (x, v) :=
  (contMDiff_chartedMk n IB IG IF).comp (contMDiff_id.prodMk contMDiff_const)

variable (n IB IG IF) in
/-- For a fixed point `x` of the total space of `P`, the inclusion `v ↦ [x, v]` of `F` onto the
fibre of the associated bundle through `[x, v]` is `C^n`. -/
theorem contMDiff_chartedMk_right [ContMDiffSMul IG IF n G F] (x : ManifoldTotalSpace G P) :
    ContMDiff IF (IB.prod IF) n fun v : F ↦ chartedMk G F P (x, v) :=
  (contMDiff_chartedMk n IB IG IF).comp (contMDiff_const.prodMk contMDiff_id)

/-- **The projection of `[x, v]` is the projection of `x`, on tangent vectors.** The derivative
of the projection of the associated bundle at `[x, v]`, composed with that of `x' ↦ [x', v]` at
`x`, is the derivative of the projection of `P` at `x`, up to the identification
`tangentSpaceCast` of the tangent spaces of the base at the two equal base points. -/
theorem mfderiv_proj_chartedMk_apply [ContMDiffSMul IG IF n G F] (hn : n ≠ 0)
    (x : ManifoldTotalSpace G P) (v : F) (w : TangentSpace (IB.prod IG) x) :
    mfderiv (IB.prod IG) IB (ManifoldTotalSpace.projContMDiffMap n G P IB IG) x w =
      tangentSpaceCast IB (πM (chartedMk G F P (x, v)))
        (ManifoldTotalSpace.projContMDiffMap n G P IB IG x)
        (mfderiv (IB.prod IF) IB πM (chartedMk G F P (x, v))
          (mfderiv (IB.prod IG) (IB.prod IF)
            (fun x' : ManifoldTotalSpace G P ↦ chartedMk G F P (x', v)) x w)) := by
  have hfun : ⇑(ManifoldTotalSpace.projContMDiffMap n G P IB IG) =ᶠ[nhds x]
      πM ∘ (fun x' : ManifoldTotalSpace G P ↦ chartedMk G F P (x', v)) :=
    .of_forall fun x' ↦ by simp
  rw [hfun.mfderiv_eq, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    mfderiv_comp_apply x ((πM).contMDiff.mdifferentiableAt hn)
      ((contMDiff_chartedMk_left n IB IF v).mdifferentiableAt hn)]
  simp only [Function.comp_apply]

/-- **The fibres of the quotient map are the orbits of the diagonal action**: `[x, v] = [y, w]`
exactly when `(y, w) = (x · g, g⁻¹ • v)` for some `g : G`. -/
theorem chartedMk_eq_chartedMk_iff {x y : ManifoldTotalSpace G P × F} :
    chartedMk G F P x = chartedMk G F P y ↔
      ∃ g : G, y = (op g • x.1, g⁻¹ • x.2) := by
  rw [chartedMk_apply, chartedMk_apply,
    (ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).injective.eq_iff,
    totalSpaceMk_mk_eq_iff (x := ((ManifoldTotalSpace.homeomorph G P).symm x.1, x.2))
      (y := ((ManifoldTotalSpace.homeomorph G P).symm y.1, y.2))]
  refine exists_congr fun g ↦ ?_
  rw [← ManifoldTotalSpace.homeomorph_symm_smul, Prod.ext_iff, Prod.ext_iff,
    (ManifoldTotalSpace.homeomorph G P).symm.injective.eq_iff]

variable [∀ b, Nonempty (P b)]

variable (n IB IF) in
/-- The tautological section of the bundle associated with `Q` over `M`: at `m` it is `m`
itself, read in the fibre of `Q ×_G F` over `m` through Tau Ceti's `pullbackEquiv`. -/
def pullbackProjSection (m : ManifoldTotalSpace F (AssociatedBundle G P F)) :
    AssociatedBundle G Q F m :=
  (pullbackEquiv πM m).symm ((ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm m).snd

variable (n IB IF) in
/-- Read in the fibre of `M` over `π_M m`, the tautological section at `m` is `m`. -/
@[simp]
theorem pullbackEquiv_pullbackProjSection (m : ManifoldTotalSpace F (AssociatedBundle G P F)) :
    pullbackEquiv πM m (pullbackProjSection n IB IF m) =
      ((ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm m).snd :=
  Equiv.apply_symm_apply _ _

variable (n IB IF) in
/-- The tautological section is `C^n`, as a map into the charted total space of `Q ×_G F`. -/
theorem contMDiff_pullbackProjSection :
    ContMDiff (IB.prod IF) ((IB.prod IF).prod IF) n fun m ↦
      ManifoldTotalSpace.homeomorph F (AssociatedBundle G Q F)
        ⟨m, pullbackProjSection n IB IF m⟩ := by
  rcases isEmpty_or_nonempty F with hF | hF
  · -- With `F` empty, so is `M`.
    intro m
    obtain ⟨-, w, -⟩ :=
      exists_mk ((ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm m).snd
    exact isEmptyElim w
  refine (contMDiff_pullbackHomeomorph_iff πM).2 <|
    (ManifoldTotalSpace.contMDiff_pullback_iff πM (πM).contMDiff).2
      ⟨contMDiff_id.congr fun m ↦ by simp only [pullbackHomeomorph_apply, id], ?_⟩
  refine contMDiff_id.congr fun m ↦ ?_
  rw [pullbackHomeomorph_apply]
  dsimp only
  rw [pullbackEquiv_pullbackProjSection]
  -- The image in `M` of `⟨m, a⟩` is `⟨π_M m, a⟩` by definition, and `π_M m` is the projection of
  -- the point of `M` that `m` stands for; `Pullback.lift_mk` does not rewrite here.
  exact (ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).apply_symm_apply m

/-- The equivariant function of the tautological section takes the value `w` at a point
`z = (m, y)` of the total space of `Q` exactly when `m` is the class `[y, w]`, with `y` read in
the total space of `P`. -/
theorem sectionFunction_pullbackProjSection_eq_iff (z : TotalSpace G Q) (w : F) :
    sectionFunction (pullbackProjSection n IB IF) z = w ↔
      (ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm z.proj =
        ⟨(Pullback.lift πM z).proj, mk G (Pullback.lift πM z).snd w⟩ := by
  obtain ⟨m, y⟩ := z
  rw [sectionFunction_eq_iff, ← (pullbackEquiv πM m).injective.eq_iff,
    pullbackEquiv_pullbackProjSection, pullbackEquiv_mk πM m y w]
  have key (t : TotalSpace F (AssociatedBundle G P F)) (a : AssociatedBundle G P F t.proj) :
      a = t.snd ↔ t = ⟨t.proj, a⟩ := by
    rw [eq_comm, ← TotalSpace.mk_inj (b := t.proj)]
  -- The image of `⟨m, y⟩` in `P` is `⟨π_M m, y⟩` by definition, and `π_M m` is the projection
  -- of the point of `M` that `m` stands for; `Pullback.lift_mk` does not rewrite here.
  exact key _ _

variable [LieGroup IG n G] [ContMDiffSMul IG IF n G F]

variable (n IB IG IF) in
/-- **`P × F` is the pull-back of `P` to the associated bundle.** The `C^n` diffeomorphism
`(x, v) ↦ ([x, v], x)` from `P × F` onto the total space of the pull-back `Q = π_M^* P` of `P` to
`M = P ×_G F`. -/
def pullbackProjDiffeomorph :
    (ManifoldTotalSpace G P × F) ≃ₘ^n⟮(IB.prod IG).prod IF, (IB.prod IF).prod IG⟯
      ManifoldTotalSpace G Q where
  toFun x := ManifoldTotalSpace.homeomorph G Q (pullbackProjMk n IB IF x)
  invFun z :=
    (ManifoldTotalSpace.homeomorph G P
        (Pullback.lift πM ((ManifoldTotalSpace.homeomorph G Q).symm z)),
      sectionFunction (pullbackProjSection n IB IF) ((ManifoldTotalSpace.homeomorph G Q).symm z))
  left_inv x := by
    refine Prod.ext ?_ ?_
    · simp [lift_pullbackProjMk]
    · refine (sectionFunction_pullbackProjSection_eq_iff _ _).2 ?_
      rw [Homeomorph.symm_apply_apply, lift_pullbackProjMk, pullbackProjMk_proj,
        homeomorph_symm_chartedMk]
  right_inv z := by
    obtain ⟨y, rfl⟩ := (ManifoldTotalSpace.homeomorph G Q).surjective z
    simp only [Homeomorph.symm_apply_apply]
    congr 1
    refine Pullback.totalSpace_ext ?_ ?_
    · rw [pullbackProjMk_proj, chartedMk_homeomorph,
        ← (sectionFunction_pullbackProjSection_eq_iff y _).1 rfl, Homeomorph.apply_symm_apply]
    · rw [lift_pullbackProjMk, Homeomorph.symm_apply_apply]
  contMDiff_toFun := by
    refine (ManifoldTotalSpace.contMDiff_pullback_iff πM (πM).contMDiff).2 ⟨?_, ?_⟩
    · simpa only [pullbackProjMk_proj] using contMDiff_chartedMk n IB IG IF
    · simp only [lift_pullbackProjMk, Homeomorph.apply_symm_apply]
      exact contMDiff_fst
  contMDiff_invFun := by
    refine (ManifoldTotalSpace.contMDiff_pullbackLift n IG πM (πM).contMDiff).prodMk ?_
    exact contMDiff_sectionFunction _ (contMDiff_pullbackProjSection n IB IF)

/-- `Φ (x, v)` is the point `([x, v], x)`. -/
theorem pullbackProjDiffeomorph_apply (x : ManifoldTotalSpace G P × F) :
    pullbackProjDiffeomorph n IB IG IF x =
      ManifoldTotalSpace.homeomorph G Q (pullbackProjMk n IB IF x) := (rfl)

/-- The inverse of `Φ` sends `(m, y)` to `(y, w)` with `[y, w] = m`. -/
theorem pullbackProjDiffeomorph_symm_apply (z : ManifoldTotalSpace G Q) :
    (pullbackProjDiffeomorph n IB IG IF).symm z =
      (ManifoldTotalSpace.homeomorph G P
          (Pullback.lift πM ((ManifoldTotalSpace.homeomorph G Q).symm z)),
        sectionFunction (pullbackProjSection n IB IF)
          ((ManifoldTotalSpace.homeomorph G Q).symm z)) := (rfl)

/-- The second coordinate of `Φ⁻¹ z`, for `z = (m, y)`, is `w` exactly when `m` is the class
`[y, w]`, with `y` read in the total space of `P`. -/
theorem pullbackProjDiffeomorph_symm_snd_eq_iff (z : ManifoldTotalSpace G Q) (w : F) :
    ((pullbackProjDiffeomorph n IB IG IF).symm z).2 = w ↔
      (ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm
          ((ManifoldTotalSpace.homeomorph G Q).symm z).proj =
        ⟨(Pullback.lift πM ((ManifoldTotalSpace.homeomorph G Q).symm z)).proj,
          mk G (Pullback.lift πM ((ManifoldTotalSpace.homeomorph G Q).symm z)).snd w⟩ := by
  rw [pullbackProjDiffeomorph_symm_apply, sectionFunction_pullbackProjSection_eq_iff]

/-- **The projection of `Q` composed with `Φ` is the quotient map** `(x, v) ↦ [x, v]`. -/
@[simp]
theorem proj_pullbackProjDiffeomorph (x : ManifoldTotalSpace G P × F) :
    ((ManifoldTotalSpace.homeomorph G Q).symm (pullbackProjDiffeomorph n IB IG IF x)).proj =
      chartedMk G F P x := by
  rw [pullbackProjDiffeomorph_apply, Homeomorph.symm_apply_apply, pullbackProjMk_proj]

variable (n IB IG IF) in
/-- **The quotient map factors through `Φ`**: it is the `C^n` projection of `Q` composed with
`Φ`. -/
theorem projContMDiffMap_comp_pullbackProjDiffeomorph :
    ⇑(ManifoldTotalSpace.projContMDiffMap n G Q (IB.prod IF) IG) ∘
        pullbackProjDiffeomorph n IB IG IF = chartedMk G F P :=
  funext fun x ↦ by
    rw [Function.comp_apply, ManifoldTotalSpace.coe_projContMDiffMap]
    exact proj_pullbackProjDiffeomorph x

/-- The image of `Φ (p, v)` in the total space of `P` is `p`. -/
@[simp]
theorem lift_pullbackProjDiffeomorph_homeomorph (p : TotalSpace G P) (v : F) :
    Pullback.lift πM ((ManifoldTotalSpace.homeomorph G Q).symm
        (pullbackProjDiffeomorph n IB IG IF (ManifoldTotalSpace.homeomorph G P p, v))) = p := by
  rw [pullbackProjDiffeomorph_apply, Homeomorph.symm_apply_apply, lift_pullbackProjMk,
    Homeomorph.symm_apply_apply]

/-- **`Φ` is equivariant**, for the diagonal action `(x, v) · g = (x · g, g⁻¹ • v)` on
`P × F` and the principal action on `Q`. -/
theorem pullbackProjDiffeomorph_smul (g : G) (x : ManifoldTotalSpace G P × F) :
    pullbackProjDiffeomorph n IB IG IF (op g • x.1, g⁻¹ • x.2) =
      op g • pullbackProjDiffeomorph n IB IG IF x := by
  rw [pullbackProjDiffeomorph_apply, pullbackProjDiffeomorph_apply,
    ManifoldTotalSpace.smul_homeomorph]
  congr 1
  refine Pullback.totalSpace_ext ?_ ?_
  · rw [pullbackProjMk_proj, pullbackProjMk_proj, chartedMk_op_smul_inv_smul]
  · rw [lift_pullbackProjMk, ManifoldTotalSpace.homeomorph_symm_smul]
    -- `Pullback.lift` of a point `⟨m, s⟩` is `⟨πM m, s⟩` by definition; `Pullback.lift_mk` does not
    -- rewrite here, since the fibre of `Q` is not reducibly that of `P`.
    exact congrArg (fun y : TotalSpace G P ↦ (⟨y.proj, op g • y.snd⟩ : TotalSpace G P))
      (lift_pullbackProjMk n IB IF x).symm

/-- **`Φ` carries fundamental fields to fundamental fields.** The derivative of `Φ` at `(x, v)`
sends the fundamental vector `(x ξ, -X_ξ(v))` of `ξ` for the diagonal action to the fundamental
vector of `ξ` for the principal action on `Q` at `Φ (x, v)`. -/
theorem mfderiv_pullbackProjDiffeomorph_fundamental (hn : 1 ≤ n) (ξ : GroupLieAlgebra IG G)
    (x : ManifoldTotalSpace G P × F) :
    mfderiv ((IB.prod IG).prod IF) ((IB.prod IF).prod IG) (pullbackProjDiffeomorph n IB IG IF) x
        (rightFundamentalVectorField (IB.prod IG) ξ x.1, -fundamentalVectorField IF ξ x.2) =
      rightFundamentalVectorField ((IB.prod IF).prod IG) ξ
        (pullbackProjDiffeomorph n IB IG IF x) := by
  have hn₀ : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  have : LieGroup IG 1 G := .of_le hn
  have : ContMDiffSMul IG IF 1 G F := .of_le hn
  have h₁ : MDifferentiableAt IG (IB.prod IG) (fun g : G ↦ op g • x.1) 1 :=
    PrincipalBundle.mdifferentiableAt_orbit (n := 1) one_ne_zero x.1 1
  have horbit : MDifferentiableAt IG IF (fun g : G ↦ g • x.2) 1 :=
    (ContMDiffSMul.contMDiff_smul_const (n := 1) x.2).mdifferentiableAt one_ne_zero
  have h₂ : MDifferentiableAt IG IF (fun g : G ↦ g⁻¹ • x.2) 1 :=
    horbit.comp_of_eq 1 ((contMDiff_inv IG 1).mdifferentiableAt one_ne_zero) inv_one
  -- The orbit map of `x` for the diagonal action sends `ξ` to `(x ξ, -X_ξ(v))`.
  have hγ : mfderiv IG ((IB.prod IG).prod IF) (fun g : G ↦ (op g • x.1, g⁻¹ • x.2)) 1 ξ =
      (rightFundamentalVectorField (IB.prod IG) ξ x.1, -fundamentalVectorField IF ξ x.2) := by
    rw [mfderiv_prodMk h₁ h₂]
    -- `(f.prod g) ξ` is `(f ξ, g ξ)` by definition; `ContinuousLinearMap.prod_apply` does not
    -- rewrite, since the tangent space of the product model is not reducibly a product.
    exact Prod.ext (rightFundamentalVectorField_apply ξ x.1).symm
      (mfderiv_inv_smul_one_apply ξ)
  -- The orbit map of `Φ x` is `Φ` composed with the orbit map of `x` for the diagonal action.
  have hcomp : (fun g : G ↦ op g • pullbackProjDiffeomorph n IB IG IF x) =
      pullbackProjDiffeomorph n IB IG IF ∘ fun g : G ↦ (op g • x.1, g⁻¹ • x.2) :=
    funext fun g ↦ (pullbackProjDiffeomorph_smul g x).symm
  calc _ = mfderiv ((IB.prod IG).prod IF) ((IB.prod IF).prod IG)
        (pullbackProjDiffeomorph n IB IG IF) x (mfderiv IG ((IB.prod IG).prod IF)
          (fun g : G ↦ (op g • x.1, g⁻¹ • x.2)) 1 ξ) := by
        -- After the rewrite, the two vectors differ only in the tangent space they are typed in.
        rw [hγ]
        rfl
    _ = _ := by
        rw [rightFundamentalVectorField_apply, hcomp]
        exact (mfderiv_comp_apply_of_eq 1
          ((pullbackProjDiffeomorph n IB IG IF).mdifferentiable hn₀ x) (h₁.prodMk h₂)
          (by simp) ξ).symm

end

section Submersion

/-! ### The quotient map is a submersion -/

variable {n : ℕ∞ω} {𝕜 B G F : Type*} [RCLike 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [FiniteDimensional 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [IB.Boundaryless]
  [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB n B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [FiniteDimensional 𝕜 EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners 𝕜 EG HG} [IG.Boundaryless]
  [Group G] [TopologicalSpace G] [ChartedSpace HG G] [LieGroup IG n G]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] [FiniteDimensional 𝕜 EF]
  {HF : Type*} [TopologicalSpace HF] {IF : ModelWithCorners 𝕜 EF HF} [IF.Boundaryless]
  [TopologicalSpace F] [ChartedSpace HF F] [IsManifold IF n F] [MulAction G F]
  [ContinuousSMul G F] [ContMDiffSMul IG IF n G F]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [ContMDiffFiberBundle n G P IB IG]

/-- The projection `π_M` of the associated bundle, as a `C^n` map. -/
local notation "πM" => ManifoldTotalSpace.projContMDiffMap n F (AssociatedBundle G P F) IB IF

/-- The pull-back `Q = π_M^* P` of `P` to the associated bundle. -/
local notation "Q" => (πM : ManifoldTotalSpace F (AssociatedBundle G P F) → B) *ᵖ P

/-- **The quotient map onto the associated bundle is a submersion.** For a `C^n` principal bundle
`P` (`1 ≤ n`) with finite-dimensional base and structure group, and a `C^n` action of `G` on a
finite-dimensional manifold `F`, all without boundary, the map `(x, v) ↦ [x, v]` from `P × F`
onto `P ×_G F` is a `C^n` submersion. -/
theorem isSubmersion_chartedMk (hn : 1 ≤ n) :
    Manifold.IsSubmersion ((IB.prod IG).prod IF) (IB.prod IF) n (chartedMk G F P) := by
  have := FiberBundle.nonempty_fiber G P
  have hn₀ : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  have : ContMDiffFiberBundle n F (AssociatedBundle G P F) IB IF := contMDiffFiberBundle IG
  -- The quotient map is the projection of `Q` composed with the diffeomorphism `Φ`.
  set Φ := pullbackProjDiffeomorph n IB IG IF (G := G) (F := F) (P := P)
  have hπ := ManifoldTotalSpace.isSubmersion_projContMDiffMap n G Q (IB.prod IF) IG
  rw [← projContMDiffMap_comp_pullbackProjDiffeomorph n IB IG IF]
  refine (ContMDiff.isSubmersionOfComplement_of_surjective_mfderiv
    (hπ.contMDiff.comp Φ.contMDiff) hn fun x ↦ ?_).isSubmersion
  rw [mfderiv_comp x (hπ.contMDiff.mdifferentiableAt hn₀) (Φ.mdifferentiable hn₀ x)]
  exact (hπ.surjective_mfderiv hn₀ _).comp
    ((Φ.isLocalDiffeomorph x).isInvertible_mfderiv hn₀).surjective

omit [FiniteDimensional 𝕜 EB] [IB.Boundaryless] [FiniteDimensional 𝕜 EG] [IG.Boundaryless]
  [FiniteDimensional 𝕜 EF] [IF.Boundaryless] in
/-- **The vertical vectors of the quotient map are the fundamental vectors of the diagonal
action.** A tangent vector to `P × F` at `(x, v)` is killed by the derivative of
`(x, v) ↦ [x, v]` exactly when it is `(x ξ, -X_ξ(v))` for some `ξ` in the Lie algebra of `G`. -/
theorem mfderiv_chartedMk_eq_zero_iff (hn : 1 ≤ n) (x : ManifoldTotalSpace G P × F)
    (w : TangentSpace ((IB.prod IG).prod IF) x) :
    mfderiv ((IB.prod IG).prod IF) (IB.prod IF) (chartedMk G F P) x w = 0 ↔
      ∃ ξ : GroupLieAlgebra IG G,
        (rightFundamentalVectorField (IB.prod IG) ξ x.1, -fundamentalVectorField IF ξ x.2) = w := by
  have := FiberBundle.nonempty_fiber G P
  have hn₀ : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  have : ContMDiffFiberBundle n F (AssociatedBundle G P F) IB IF := contMDiffFiberBundle IG
  set Φ := pullbackProjDiffeomorph n IB IG IF (G := G) (F := F) (P := P)
  have hπ := ManifoldTotalSpace.isSubmersion_projContMDiffMap n G Q (IB.prod IF) IG
  -- The quotient map is the projection of `Q` composed with `Φ`, whose derivative is injective;
  -- the kernel of the derivative of the projection consists of the fundamental vectors of `Q`.
  have h0 : mfderiv ((IB.prod IG).prod IF) (IB.prod IF) (chartedMk G F P) x w =
      mfderiv ((IB.prod IF).prod IG) (IB.prod IF)
        (ManifoldTotalSpace.projContMDiffMap n G Q (IB.prod IF) IG) (Φ x)
          (mfderiv ((IB.prod IG).prod IF) ((IB.prod IF).prod IG) Φ x w) := by
    rw [← projContMDiffMap_comp_pullbackProjDiffeomorph n IB IG IF]
    exact mfderiv_comp_apply x (hπ.contMDiff.mdifferentiableAt hn₀) (Φ.mdifferentiable hn₀ x) w
  have : LieGroup IG 1 G := .of_le hn
  have : ContMDiffFiberBundle 1 G Q (IB.prod IF) IG := .of_le hn
  have hker := PrincipalBundle.range_rightFundamentalLinearMap_eq_ker_mfderiv_proj
    (IB := IB.prod IF) (IG := IG) (Φ x)
  -- Tau Ceti states the kernel with the projection written out as a function.
  rw [← ManifoldTotalSpace.coe_projContMDiffMap (n := n) (IB := IB.prod IF) (IF := IG)] at hker
  constructor
  · intro hw
    have hk : mfderiv ((IB.prod IG).prod IF) ((IB.prod IF).prod IG) Φ x w ∈
        LinearMap.range (PrincipalBundle.rightFundamentalLinearMap (IB.prod IF) IG (Φ x)) := by
      rw [hker, LinearMap.mem_ker]
      exact h0.symm.trans hw
    obtain ⟨ξ, hξ⟩ := hk
    refine ⟨ξ, ((Φ.isLocalDiffeomorph x).isInvertible_mfderiv hn₀).injective ?_⟩
    rw [PrincipalBundle.rightFundamentalLinearMap_apply] at hξ
    exact (mfderiv_pullbackProjDiffeomorph_fundamental hn ξ x).trans hξ
  · rintro ⟨ξ, rfl⟩
    rw [h0, ManifoldTotalSpace.coe_projContMDiffMap (n := n) (IB := IB.prod IF) (IF := IG)]
    exact (congrArg _ (mfderiv_pullbackProjDiffeomorph_fundamental hn ξ x)).trans
      (PrincipalBundle.mfderiv_proj_rightFundamentalVectorField _ ξ)

end Submersion

section Descent

/-! ### Descent of invariant forms along the quotient map -/

variable {B G F : Type*}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  [LieGroup IG ∞ G]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} [TopologicalSpace F] [ChartedSpace HF F] [IsManifold IF ∞ F]
  [MulAction G F] [ContinuousSMul G F] [ContMDiffSMul IG IF ∞ G F]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [ContMDiffFiberBundle ∞ G P IB IG]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}

/-- **Invariant forms vanishing on fundamental vectors are basic for the quotient map.** A smooth
form on `P × F` that is invariant under the diagonal action `(x, v) ↦ (x · g, g⁻¹ • v)` and
vanishes as soon as one of its arguments at `(x, v)` is `(x ξ, -X_ξ(v))` for some `ξ` in the Lie
algebra of `G` is basic for the quotient map `(x, v) ↦ [x, v]` onto `P ×_G F`. -/
theorem isBasic_chartedMk
    {β : SmoothForm ((IB.prod IG).prod IF) (ManifoldTotalSpace G P × F) V k}
    (hβ : ∀ g : G, SmoothForm.mpullback
      (fun x : ManifoldTotalSpace G P × F ↦ (op g • x.1, g⁻¹ • x.2))
      (contMDiff_op_smul_inv_smul g) β = β)
    (hfund : ∀ (x : ManifoldTotalSpace G P × F)
      (v : Fin k → TangentSpace ((IB.prod IG).prod IF) x) (j : Fin k) (ξ : GroupLieAlgebra IG G),
      v j = (rightFundamentalVectorField (IB.prod IG) ξ x.1, -fundamentalVectorField IF ξ x.2) →
        β.val x v = 0) :
    RoughForm.IsBasic (V := V) (IB.prod IF) (chartedMk G F P) β.val := by
  refine RoughForm.isBasic_of_mpullback_eq
    (σ := fun (g : G) (x : ManifoldTotalSpace G P × F) ↦ (op g • x.1, g⁻¹ • x.2))
    ((contMDiff_chartedMk ∞ IB IG IF).mdifferentiable (by simp))
    (fun g ↦ (contMDiff_op_smul_inv_smul (n := ∞) g).mdifferentiable (by simp))
    (fun g ↦ funext (chartedMk_op_smul_inv_smul g))
    (fun x y hxy ↦ Or.inr ((chartedMk_eq_chartedMk_iff.1 hxy).imp fun _ h ↦ h.symm))
    (fun x v j hj ↦ ?_) fun g ↦ ?_
  · obtain ⟨ξ, hξ⟩ := (mfderiv_chartedMk_eq_zero_iff ENat.LEInfty.out x (v j)).1 hj
    exact hfund x v j ξ hξ.symm
  · rw [← SmoothForm.coe_mpullback _ (contMDiff_op_smul_inv_smul g), hβ]

/-- **Descent of invariant forms to the associated bundle.** A smooth form `β` on `P × F` that is
invariant under the diagonal action `(x, v) ↦ (x · g, g⁻¹ • v)` and vanishes as soon as one of
its arguments at `(x, v)` is `(x ξ, -X_ξ(v))` for some `ξ` in the Lie algebra of `G` is the
pull-back of exactly one smooth form on `P ×_G F` along the quotient map `(x, v) ↦ [x, v]`. -/
theorem existsUnique_mpullback_chartedMk_eq [FiniteDimensional ℝ EB] [IB.Boundaryless]
    [FiniteDimensional ℝ EG] [IG.Boundaryless] [FiniteDimensional ℝ EF] [IF.Boundaryless]
    [ContMDiffFiberBundle ∞ F (AssociatedBundle G P F) IB IF]
    {β : SmoothForm ((IB.prod IG).prod IF) (ManifoldTotalSpace G P × F) V k}
    (hβ : ∀ g : G, SmoothForm.mpullback
      (fun x : ManifoldTotalSpace G P × F ↦ (op g • x.1, g⁻¹ • x.2))
      (contMDiff_op_smul_inv_smul g) β = β)
    (hfund : ∀ (x : ManifoldTotalSpace G P × F)
      (v : Fin k → TangentSpace ((IB.prod IG).prod IF) x) (j : Fin k) (ξ : GroupLieAlgebra IG G),
      v j = (rightFundamentalVectorField (IB.prod IG) ξ x.1, -fundamentalVectorField IF ξ x.2) →
        β.val x v = 0) :
    ∃! γ : SmoothForm (IB.prod IF) (ManifoldTotalSpace F (AssociatedBundle G P F)) V k,
      SmoothForm.mpullback (chartedMk G F P) (contMDiff_chartedMk ∞ IB IG IF) γ = β := by
  have hq := isSubmersion_chartedMk (n := ∞) (IB := IB) (IG := IG) (IF := IF) (G := G)
    (F := F) (P := P) ENat.LEInfty.out
  exact ⟨_, SmoothForm.mpullback_descendedForm (hf := hq) (hsurj := surjective_chartedMk)
    (hα := isBasic_chartedMk hβ hfund), fun _ ↦ SmoothForm.eq_descendedForm_iff.2⟩

end Descent

end TauCeti.AssociatedBundle
