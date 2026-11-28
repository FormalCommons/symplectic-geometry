/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Fibration.HorizontalDistribution
public import SymplecticGeometry.Geometry.Manifold.Submersion.Curvature
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.StructureGroup
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
public import SymplecticGeometry.Geometry.Symplectic.Fibration.LocalForm
import SymplecticGeometry.Geometry.Manifold.Submersion.VerticalProjection
import TauCeti.Geometry.Manifold.Distribution.Kernel
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.MixedPartial
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod
import SymplecticGeometry.Geometry.Manifold.VectorField.Prod
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic
import TauCeti.Geometry.Manifold.VectorField.ModelChart

/-!
# The curvature of the connection of a two-form

Let `τ` be a two-form on `M` and `proj : M → B` a map such that the `τ`-orthogonals of the
vertical spaces form an Ehresmann connection `hD` (for a smooth submersion this holds when `τ` is
vertically nondegenerate, `TauCeti.SmoothTwoForm.IsVerticallyNondegenerate.isEhresmannConnection`).
Lifting a field `v` on `B` horizontally gives `v♯`. This file shows that the
curvature of `hD` is determined, through `τ`, by the function `τ(v₁♯, v₂♯)` and the exterior
derivative of `τ`: for every vertical vector `η` at `x`,

`τ(Ω(v₁, v₂), η) = η(τ(v₁♯, v₂♯)) - dτ(v₁♯, v₂♯, η)`,

where `Ω(v₁, v₂) = [v₁♯, v₂♯] - [v₁, v₂]♯` is `hD.curvature v₁ v₂`. No closedness of `τ` is
assumed. When `τ` is closed, the last term vanishes, and the identity says that on each fibre the
contraction of `τ` with the curvature is the differential of the restriction of `τ(v₁♯, v₂♯)`.

As a consequence, two closed two-forms `τ` and `τ'` that agree whenever one argument is vertical
(so that they have the same connection) give functions `τ(v₁♯, v₂♯)` and `τ'(v₁♯, v₂♯)` with
the same derivative along every vertical vector: both sides of the identity for `τ'` agree with
those for `τ`.

The proof follows Guillemin–Lerman–Sternberg [GuilleminLermanSternberg1996], §1.3–1.4. Extend `η`
to a vertical vector field `W` (the vertical projection of a local extension of `η`) and expand
`dτ(v₁♯, v₂♯, W)` by the invariant formula `TauCeti.SmoothForm.mextDeriv_apply_two`. The
functions `τ(vᵢ♯, W)` vanish identically, since horizontal vectors are `τ`-orthogonal to vertical
ones. The brackets `[vᵢ♯, W]` are vertical, since `vᵢ♯` is `proj`-related to `vᵢ` and `W` to `0`
(`ContMDiffAt.mlieBracket_mem_ker_mfderiv_of_eventually_related`), so their pairings with the
lifts vanish too. In the remaining bracket term, `[v₁♯, v₂♯]` differs from the curvature by the
horizontal field `[v₁, v₂]♯`, which `τ` pairs with `W` to zero.

On signs: the bracket is Mathlib's `VectorField.mlieBracket`, as in [GuilleminLermanSternberg1996];
in McDuff–Salamon [McDuffSalamon2017], Lemma 6.4.8, the bracket and so the curvature have the
opposite sign (see also the errata [McDuffSalamon2019Errata]).

The file then reads the curvature on one fibre through a trivialization `e` of `proj`: the
field `hD.curvatureIn IF e b v₁ v₂` on the model fibre `F` is the image of the curvature at
`e⁻¹ (b, y)` under the derivative of the fibre coordinate of `e`. Since the curvature is vertical,
a change of trivialization acts on it by the derivative of the coordinate change. For an atlas `A`
of `proj` and a two-form `σ` on `F`, the connection has Hamiltonian curvature when every such
field is a Hamiltonian vector field of a smooth function on `F`, in Tau Ceti's sign
(`ι_X σ = df`). For an atlas whose coordinate changes preserve `σ`, one chart at each point
suffices, since a diffeomorphism that preserves `σ` carries Hamiltonian vector fields to
Hamiltonian vector fields (Tau Ceti's `TauCeti.SmoothTwoForm.IsHamiltonianVectorField.mpullback`).
This is the curvature condition of McDuff–Salamon [McDuffSalamon2017], Exercise 6.4.9, and of
[GuilleminLermanSternberg1996], §1.4.

Last, the file computes the curvature in a product chart, in the setting of `LocalForm.lean`: a
two-form `τ` on `EB × F` with fibre components `σ(x)`, mixed components `αᵢ(x)` and the fields
`Xᵢ(x)` with `ι(Xᵢ(x)) σ(x) = αᵢ(x)`, so that the horizontal lift of the constant field `bs i`
is `(bs i, Xᵢ(x))`. If `σ(x)` is nondegenerate and `τ` is vertically closed at `(x, y)`, the
curvature `V` of `bs i, bs j` at `(x, y)` is vertical and
`σ(x)(V, ·) = ∂ᵢαⱼ(x) - ∂ⱼαᵢ(x) - d(σ(x)(Xᵢ(x), Xⱼ(x)))` at `y`. This is the formula of the
hint to [McDuffSalamon2017], Exercise 6.4.9, with the curvature of Mathlib's bracket, which has
the opposite sign to the book's (see the note on signs above). The proof needs no bracket of
the lifts: it evaluates the curvature identity on `(0, w)`. On the fibre over `x`, the lifts
`Lᵢ`, `Lⱼ` have `τ(Lᵢ, Lⱼ) = τ((bs i, 0), (bs j, 0)) - σ(x)(Xᵢ, Xⱼ)`; vertical
closedness reduces `dτ(Lᵢ, Lⱼ, (0, w))` to
`dτ((bs i, 0), (bs j, 0), (0, w))`, which Tau Ceti's
`TauCeti.SmoothForm.mextDeriv_apply_eq_fderiv_sub_fderiv_add_mvfderiv` expands into derivatives
of `αⱼ` and `αᵢ` along the base and of `τ((bs i, 0), (bs j, 0))` along `F`.

## Main definitions

* `TauCeti.IsEhresmannConnection.curvatureIn`: the curvature on the fibre over a point, read in
  a trivialization as a vector field on the model fibre.
* `TauCeti.IsEhresmannConnection.HasHamiltonianCurvature`: the curvature read in every chart of
  an atlas is Hamiltonian for a two-form on the fibre.

## Main results

* `TauCeti.IsEhresmannConnection.apply_curvature_eq_mvfderiv_sub_mextDeriv`: the curvature
  identity for the connection of a two-form.
* `TauCeti.IsEhresmannConnection.mvfderiv_val_horizontalLiftField_eq_of_isClosed`: for two
  closed forms with the same connection, `τ(v₁♯, v₂♯)` and `τ'(v₁♯, v₂♯)` have the same
  derivative along vertical vectors.
* `TauCeti.IsEhresmannConnection.curvatureIn_coordChange`: the curvature read in two
  trivializations differs by the derivative of the coordinate change.
* `TauCeti.IsEhresmannConnection.hasHamiltonianCurvature_iff_forall_exists`: for an atlas whose
  coordinate changes preserve `σ`, Hamiltonian curvature can be checked in one chart per point.
* `TauCeti.IsEhresmannConnection.hasHamiltonianCurvature_of_curvature_eq_zero`: a connection with
  vanishing curvature has Hamiltonian curvature.
* `TauCeti.IsEhresmannConnection.curvatureIn_local`: the curvature of two constant fields in a
  product chart, through the components of the local form.

## References

* [V. Guillemin, E. Lerman, S. Sternberg, *Symplectic Fibrations and Multiplicity
  Diagrams*][GuilleminLermanSternberg1996], §1.3–1.4.
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Lemma 6.4.8 and Exercise 6.4.9.
* [D. McDuff and D. Salamon, *Errata*][McDuffSalamon2019Errata]
-/

public section

noncomputable section

open Bundle Filter VectorField
open scoped Manifold ContDiff

namespace TauCeti.IsEhresmannConnection

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [CompleteSpace EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B] [IsManifold IB 2 B]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [CompleteSpace EM] {HM : Type*}
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M]
  [ChartedSpace HM M] [IsManifold IM ∞ M]
  {proj : M → B} {τ : SmoothTwoForm IM M} {n : ℕ∞ω}

attribute [local instance] IsManifold.minSmoothness_of_isRCLikeNormedField

/-- **The curvature identity.** Let `hD` be the connection of a two-form `τ` on `M`: the
`τ`-orthogonals of the vertical spaces of a `C^2` map `proj : M → B`, assumed to form a `C^n`
Ehresmann connection with `1 ≤ n`. Let `v₁ v₂` be vector fields on `B`, `C^1` at `proj x`, with
horizontal lifts `v₁♯ v₂♯`. Then for every vertical vector `η` at `x`, `τ` pairs the curvature
`[v₁♯, v₂♯] - [v₁, v₂]♯` with `η` to the derivative of `τ(v₁♯, v₂♯)` along `η` minus
`dτ(v₁♯, v₂♯, η)`.

Milestone: *Curvature identity for symplectic connections*. -/
theorem apply_curvature_eq_mvfderiv_sub_mextDeriv
    (hD : IsEhresmannConnection IM IB n proj (SmoothTwoForm.horizontalDistribution IB proj τ))
    (hn : 1 ≤ n) (hproj : ContMDiff IM IB 2 proj) {v₁ v₂ : Π b : B, TangentSpace IB b} {x : M}
    (hv₁ : ContMDiffAt IB IB.tangent 1 (T% v₁) (proj x))
    (hv₂ : ContMDiffAt IB IB.tangent 1 (T% v₂) (proj x))
    {η : TangentSpace IM x} (hη : η ∈ (mfderiv IM IB proj x).ker) :
    τ.val x ![hD.curvature v₁ v₂ x, η] =
      mvfderiv IM (fun y ↦ τ.val y ![hD.horizontalLiftField v₁ y, hD.horizontalLiftField v₂ y])
          x η -
        mextDeriv τ.val x ![hD.horizontalLiftField v₁ x, hD.horizontalLiftField v₂ x, η] := by
  -- A vertical field `W` through `η`: the vertical part of a local extension of `η`.
  -- Read as a `C^1` connection, `hD` has a `C^1` vertical projection, `proj` being `C^2`.
  have hD₁ := hD.of_le hn
  obtain ⟨W, hWdef⟩ : ∃ W : Π y : M, TangentSpace IM y,
      W = fun y ↦ hD₁.verticalProjection y (FiberBundle.extend EM η y) := ⟨_, rfl⟩
  have hWx : W x = η := by
    simp only [hWdef, FiberBundle.extend_apply_self, hD₁.verticalProjection_apply_of_mem_ker hη]
  have hWv (y : M) : W y ∈ (mfderiv IM IB proj y).ker := by
    rw [hWdef]
    exact hD₁.verticalProjection_apply_mem y _
  have hW : MDifferentiableAt IM IM.tangent (T% W) x := by
    have h1 := hD₁.contMDiff_totalSpace_verticalProjection (by rwa [one_add_one_eq_two])
    have h2 := (h1 _).comp x (FiberBundle.contMDiffAt_extend (k := 1) (I := IM) EM η)
    rw [hWdef]
    exact h2.mdifferentiableAt one_ne_zero
  have hpx : ContMDiffAt IM IB 2 proj x := hproj x
  have hU := hD.mdifferentiableAt_horizontalLiftField hn hpx hv₁
  have hV := hD.mdifferentiableAt_horizontalLiftField hn hpx hv₂
  -- The brackets of the lifts with `W` are vertical.
  have hbr {v : Π b : B, TangentSpace IB b} (hv : ContMDiffAt IB IB.tangent 1 (T% v) (proj x)) :
      mlieBracket IM (hD.horizontalLiftField v) W x ∈ (mfderiv IM IB proj x).ker :=
    hpx.mlieBracket_mem_ker_mfderiv_of_eventually_related (by simp)
      (hD.mdifferentiableAt_horizontalLiftField hn hpx hv) hW
      (hv.mdifferentiableAt one_ne_zero)
      (.of_forall fun y ↦ hD.mfderiv_horizontalLiftField v y) (.of_forall hWv)
  have hzero {v : Π b : B, TangentSpace IB b} :
      (fun y ↦ τ.val y ![hD.horizontalLiftField v y, W y]) = 0 :=
    funext fun y ↦ SmoothTwoForm.val_eq_zero_of_mem_horizontalDistribution_of_mem_ker
        (hD.horizontalLiftField_mem v y) (hWv y)
  have h := SmoothForm.mextDeriv_apply_two (φ := τ) hU hV hW
  rw [hzero, hzero, mvfderiv_zero, hWx,
    SmoothTwoForm.val_eq_zero_of_mem_ker_of_mem_horizontalDistribution (hbr hv₁)
      (hD.horizontalLiftField_mem v₂ x),
    SmoothTwoForm.val_eq_zero_of_mem_ker_of_mem_horizontalDistribution (hbr hv₂)
      (hD.horizontalLiftField_mem v₁ x)] at h
  -- The bracket of the lifts is the curvature plus the horizontal lift of the bracket.
  have hsplit : mlieBracket IM (hD.horizontalLiftField v₁) (hD.horizontalLiftField v₂) x =
      hD.curvature v₁ v₂ x + hD.horizontalLiftField (mlieBracket IB v₁ v₂) x := by
    rw [curvature_apply, sub_add_cancel]
  have hlift := SmoothTwoForm.val_eq_zero_of_mem_horizontalDistribution_of_mem_ker
    (hD.horizontalLiftField_mem (mlieBracket IB v₁ v₂) x) hη
  rw [hsplit, ContinuousAlternatingMap.vecCons_add, hlift, add_zero] at h
  rw [h, zero_apply, zero_apply]
  abel

/-- **Closed forms with the same connection.** Let `τ` and `τ'` be closed two-forms that agree on
`(η, v)` for every vertical vector `η` and every tangent vector `v`, so that they have the same
horizontal spaces, and let `hD` be the connection of `τ`, a `C^n` Ehresmann connection with
`1 ≤ n` on a `C^2` map `proj`. Let `v₁ v₂` be vector fields on `B`, `C^1` at `proj x`. Then the
functions `τ'(v₁♯, v₂♯)` and `τ(v₁♯, v₂♯)` have the same derivative along every vertical vector
`η` at `x`. -/
theorem mvfderiv_val_horizontalLiftField_eq_of_isClosed
    (hD : IsEhresmannConnection IM IB n proj (SmoothTwoForm.horizontalDistribution IB proj τ))
    (hn : 1 ≤ n) (hproj : ContMDiff IM IB 2 proj) {τ' : SmoothTwoForm IM M}
    (hτ : τ.IsClosed) (hτ' : τ'.IsClosed)
    (h : ∀ y, ∀ η ∈ (mfderiv IM IB proj y).ker, ∀ v : TangentSpace IM y,
      τ.bilinFormAt y η v = τ'.bilinFormAt y η v)
    {v₁ v₂ : Π b : B, TangentSpace IB b} {x : M}
    (hv₁ : ContMDiffAt IB IB.tangent 1 (T% v₁) (proj x))
    (hv₂ : ContMDiffAt IB IB.tangent 1 (T% v₂) (proj x))
    {η : TangentSpace IM x} (hη : η ∈ (mfderiv IM IB proj x).ker) :
    mvfderiv IM (fun y ↦ τ'.val y ![hD.horizontalLiftField v₁ y, hD.horizontalLiftField v₂ y])
        x η =
      mvfderiv IM (fun y ↦ τ.val y ![hD.horizontalLiftField v₁ y, hD.horizontalLiftField v₂ y])
        x η := by
  -- `τ` and `τ'` have the same horizontal spaces, so `hD` is also the connection of `τ'`.
  have hdist : SmoothTwoForm.horizontalDistribution IB proj τ =
      SmoothTwoForm.horizontalDistribution IB proj τ' :=
    SmoothTwoForm.horizontalDistribution_eq_of_forall h
  have key : ∀ D (hD' : IsEhresmannConnection IM IB n proj D),
      D = SmoothTwoForm.horizontalDistribution IB proj τ' →
      τ'.val x ![hD'.curvature v₁ v₂ x, η] =
        mvfderiv IM (fun y ↦ τ'.val y ![hD'.horizontalLiftField v₁ y,
            hD'.horizontalLiftField v₂ y]) x η -
          mextDeriv τ'.val x ![hD'.horizontalLiftField v₁ x, hD'.horizontalLiftField v₂ x, η] := by
    rintro D hD' rfl
    exact apply_curvature_eq_mvfderiv_sub_mextDeriv hD' hn hproj hv₁ hv₂ hη
  have h' := key _ hD hdist
  have h₀ := apply_curvature_eq_mvfderiv_sub_mextDeriv hD hn hproj hv₁ hv₂ hη
  rw [(SmoothForm.isClosed_def τ).1 hτ] at h₀
  rw [(SmoothForm.isClosed_def τ').1 hτ'] at h'
  -- `τ` and `τ'` pair the curvature with the vertical vector `η` alike.
  have hΩ : τ'.val x ![hD.curvature v₁ v₂ x, η] = τ.val x ![hD.curvature v₁ v₂ x, η] := by
    have hη' := h x η hη (hD.curvature v₁ v₂ x)
    rw [SmoothForm.bilinFormAt_apply, SmoothForm.bilinFormAt_apply] at hη'
    rw [← SmoothBundleForm.eval₂_apply τ', ← SmoothBundleForm.eval₂_apply τ,
      SmoothBundleForm.eval₂_swap τ', SmoothBundleForm.eval₂_swap τ, hη']
  exact sub_left_injective (h'.symm.trans (hΩ.trans h₀))

end TauCeti.IsEhresmannConnection

/-! ### The curvature read in a trivialization -/

namespace TauCeti.IsEhresmannConnection

section CurvatureIn

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*}
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M]
  [ChartedSpace HM M] [IsManifold IM 1 M]
  {proj : M → B} {D : Π x : M, Submodule ℝ (TangentSpace IM x)} {n : ℕ∞ω}
  (hD : IsEhresmannConnection IM IB n proj D)

/-- **The curvature on a fibre, read in a trivialization.** For a trivialization `e` of `proj`
with fibre `F`, a point `b` of the base and vector fields `v₁ v₂` on `B`, the vector field on `F`
whose value at `y` is the image of the curvature `hD.curvature v₁ v₂` at `e⁻¹ (b, y)` under the
derivative of the fibre coordinate `x ↦ (e x).2` of `e`. When `b ∈ e.baseSet` and the curvature
is vertical, this is the curvature on the fibre over `b`, carried to `F` by `e`. -/
def curvatureIn (IF : ModelWithCorners ℝ EF HF) (e : Trivialization F proj) (b : B)
    (v₁ v₂ : Π b : B, TangentSpace IB b) : Π y : F, TangentSpace IF y := fun y ↦
  mfderiv IM IF (fun x ↦ (e x).2) (e.toOpenPartialHomeomorph.symm (b, y))
    (hD.curvature v₁ v₂ (e.toOpenPartialHomeomorph.symm (b, y)))

theorem curvatureIn_def (IF : ModelWithCorners ℝ EF HF) (e : Trivialization F proj) (b : B)
    (v₁ v₂ : Π b : B, TangentSpace IB b) (y : F) :
    hD.curvatureIn IF e b v₁ v₂ y =
      mfderiv IM IF (fun x ↦ (e x).2) (e.toOpenPartialHomeomorph.symm (b, y))
        (hD.curvature v₁ v₂ (e.toOpenPartialHomeomorph.symm (b, y))) :=
  (rfl)

/-! ### Hamiltonian curvature -/

section Hamiltonian

variable [IsManifold IB 1 B] [IsManifold IF ∞ F]

/-- **Hamiltonian curvature.** For an atlas `A` of `proj` with fibre `F` and a two-form `σ` on
`F`, the connection `hD` has *Hamiltonian curvature* when, for every chart `e = A.trivAt b'`,
every point `b` of its base set and all smooth vector fields `v₁ v₂` on `B`, the curvature on the
fibre over `b` read in `e`, `hD.curvatureIn IF e b v₁ v₂`, is a Hamiltonian vector field
(`ι_X σ = df`, Tau Ceti's sign) of some smooth function `f : F → ℝ`. -/
def HasHamiltonianCurvature (A : MapFiber.Atlas F proj) (σ : SmoothTwoForm IF F) : Prop :=
  ∀ b' b, b ∈ (A.trivAt b').baseSet → ∀ v₁ v₂ : Π b : B, TangentSpace IB b,
    ContMDiff IB IB.tangent ∞ (T% v₁) → ContMDiff IB IB.tangent ∞ (T% v₂) →
      ∃ f : F → ℝ, ContMDiff IF 𝓘(ℝ) ∞ f ∧
        σ.IsHamiltonianVectorField f (hD.curvatureIn IF (A.trivAt b') b v₁ v₂)

theorem hasHamiltonianCurvature_def (A : MapFiber.Atlas F proj) (σ : SmoothTwoForm IF F) :
    hD.HasHamiltonianCurvature A σ ↔
      ∀ b' b, b ∈ (A.trivAt b').baseSet → ∀ v₁ v₂ : Π b : B, TangentSpace IB b,
        ContMDiff IB IB.tangent ∞ (T% v₁) → ContMDiff IB IB.tangent ∞ (T% v₂) →
          ∃ f : F → ℝ, ContMDiff IF 𝓘(ℝ) ∞ f ∧
            σ.IsHamiltonianVectorField f (hD.curvatureIn IF (A.trivAt b') b v₁ v₂) :=
  Iff.rfl

/-- A connection whose curvature vanishes on smooth vector fields has Hamiltonian curvature, for
every atlas and every two-form on the fibre: the curvature read in a chart is the zero field,
a Hamiltonian vector field of the zero function. -/
theorem hasHamiltonianCurvature_of_curvature_eq_zero
    (h : ∀ v₁ v₂ : Π b : B, TangentSpace IB b, ContMDiff IB IB.tangent ∞ (T% v₁) →
      ContMDiff IB IB.tangent ∞ (T% v₂) → hD.curvature v₁ v₂ = 0)
    (A : MapFiber.Atlas F proj) (σ : SmoothTwoForm IF F) : hD.HasHamiltonianCurvature A σ := by
  intro b' b _ v₁ v₂ hv₁ hv₂
  refine ⟨fun _ ↦ 0, contMDiff_const, ?_⟩
  have hzero : hD.curvatureIn IF (A.trivAt b') b v₁ v₂ = 0 := funext fun y ↦ by
    rw [curvatureIn_def, h v₁ v₂ hv₁ hv₂, Pi.zero_apply, Pi.zero_apply]
    -- The derivative lands in the tangent space of `F` at the fibre coordinate of
    -- `e⁻¹ (b, y)`, which is that at `y` only by definition.
    exact map_zero _
  rw [hzero]
  exact SmoothTwoForm.isHamiltonianVectorField_const 0

end Hamiltonian

variable [CompleteSpace EB] [CompleteSpace EM] [IsManifold IM 2 M] [IsManifold IB 2 B]

attribute [local instance] IsManifold.minSmoothness_of_isRCLikeNormedField

/-- **Change of trivialization.** Let `hD` be a `C^n` Ehresmann connection, `1 ≤ n`, on a `C^2`
map `proj`, and `v₁ v₂` vector fields on `B` that are `C^1` at `b`. For trivializations `e` and
`e'` that are differentiable with differentiable inverses and contain `b` in their base sets,
the curvature on the fibre over `b` read in `e'` is the push-forward of the one read in `e` by the
coordinate change from `e` to `e'` over `b`. -/
theorem curvatureIn_coordChange (hn : 1 ≤ n) (hproj : ContMDiff IM IB 2 proj)
    {e e' : Trivialization F proj}
    (he : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF))
    (he' : e'.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) {b : B}
    (hb : b ∈ e.baseSet) (hb' : b ∈ e'.baseSet) {v₁ v₂ : Π b : B, TangentSpace IB b}
    (hv₁ : ContMDiffAt IB IB.tangent 1 (T% v₁) b) (hv₂ : ContMDiffAt IB IB.tangent 1 (T% v₂) b)
    (y : F) :
    hD.curvatureIn IF e' b v₁ v₂ (e.coordChange e' b y) =
      mfderiv IF IF (e.coordChange e' b) y (hD.curvatureIn IF e b v₁ v₂ y) := by
  have hx := e.proj_fiberInclusionMap hb y
  have hker := hD.curvature_mem_ker hn (hproj (e.fiberInclusionMap hb y)) (v₁ := v₁) (v₂ := v₂)
    (by rwa [hx]) (by rwa [hx])
  rw [curvatureIn_def, curvatureIn_def, ← e'.fiberInclusionMap_apply hb',
    e.fiberInclusionMap_coordChange e' hb hb', ← e.fiberInclusionMap_apply hb]
  exact Bundle.Trivialization.mfderiv_snd_apply_of_mfderiv_proj_eq_zero he he' hb hb' y hker

variable [IsManifold IF ∞ F]

/-- **One chart per point suffices.** Let `A` be a smooth atlas whose coordinate changes preserve
`σ`, and `hD` a `C^n` Ehresmann connection, `1 ≤ n`. Then `hD` has Hamiltonian curvature exactly
when every point `b` of the base lies in the base set of a chart of `A` in which the curvature on
the fibre over `b` is Hamiltonian for all smooth `v₁ v₂`: the coordinate changes carry the
curvature read in one chart to the curvature read in another (`curvatureIn_coordChange`), and,
preserving `σ`, Hamiltonian vector fields to Hamiltonian vector fields. -/
theorem hasHamiltonianCurvature_iff_forall_exists (hn : 1 ≤ n)
    {A : MapFiber.Atlas F proj} (hA : A.IsContMDiff ∞ IB IF IM) {σ : SmoothTwoForm IF F}
    (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ)) :
    hD.HasHamiltonianCurvature A σ ↔
      ∀ b, ∃ b', b ∈ (A.trivAt b').baseSet ∧ ∀ v₁ v₂ : Π b : B, TangentSpace IB b,
        ContMDiff IB IB.tangent ∞ (T% v₁) → ContMDiff IB IB.tangent ∞ (T% v₂) →
          ∃ f : F → ℝ, ContMDiff IF 𝓘(ℝ) ∞ f ∧
            σ.IsHamiltonianVectorField f (hD.curvatureIn IF (A.trivAt b') b v₁ v₂) := by
  refine ⟨fun h b ↦ ⟨b, A.mem_baseSet_trivAt b, h b b (A.mem_baseSet_trivAt b)⟩, ?_⟩
  intro h b'' b hb'' v₁ v₂ hv₁ hv₂
  obtain ⟨b', hb', hb'f⟩ := h b
  obtain ⟨f, hf, hX⟩ := hb'f v₁ v₂ hv₁ hv₂
  -- The coordinate change from the chart at `b''` to the chart at `b'` preserves `σ`.
  obtain ⟨ψ, hψH, hψ⟩ := MapFiber.Atlas.hasStructureGroup_iff.1 hH b'' b' b hb'' hb'
  have hXY (z : F) : mfderiv IF IF ψ z (hD.curvatureIn IF (A.trivAt b'') b v₁ v₂ z) =
      hD.curvatureIn IF (A.trivAt b') b v₁ v₂ (ψ z) := by
    rw [hψ]
    exact (hD.curvatureIn_coordChange hn (hA.contMDiff_proj.of_le (by simp))
      (hA.mdifferentiable_trivAt (by simp) b'') (hA.mdifferentiable_trivAt (by simp) b') hb'' hb'
      ((hv₁ b).of_le (by simp)) ((hv₂ b).of_le (by simp)) z).symm
  refine ⟨f ∘ ψ, hf.comp ψ.contMDiff, ?_⟩
  have h := hX.mpullback ψ.contMDiff (fun z ↦ (hf (ψ z)).mdifferentiableAt (by simp)) hXY
  rwa [SmoothForm.mem_diffeomorphStabilizer.1 hψH] at h

end CurvatureIn

end TauCeti.IsEhresmannConnection

/-! ### The curvature in a product chart -/

namespace TauCeti.IsEhresmannConnection

section Local

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [CompleteSpace EB]
  {EF HF F : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [CompleteSpace EF]
  [FiniteDimensional ℝ EF] [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF}
  [TopologicalSpace F] [ChartedSpace HF F] [IsManifold IF ∞ F]
  {ι : Type*} {τ : SmoothTwoForm (𝓘(ℝ, EB).prod IF) (EB × F)} {n : ℕ∞ω}
  (hD : IsEhresmannConnection (𝓘(ℝ, EB).prod IF) 𝓘(ℝ, EB) n Prod.fst
    (SmoothTwoForm.horizontalDistribution 𝓘(ℝ, EB) Prod.fst τ))
  (bs : Module.Basis ι ℝ EB) {x : EB} (hσ : (τ.smoothFiberComponent x).IsNondegenerate)

attribute [local instance] IsManifold.minSmoothness_of_isRCLikeNormedField

include hσ

omit [CompleteSpace EB] [CompleteSpace EF] in
/-- The horizontal lift of the constant field `bs k` at `(x, y')`, split as `(bs k, 0)` plus the
vertical vector `(0, Xₖ(x)(y'))`. -/
private theorem horizontalLiftField_const_eq_add (k : ι) (y' : F) :
    hD.horizontalLiftField (fun _ ↦ bs k : Π b : EB, TangentSpace 𝓘(ℝ, EB) b) (x, y') =
      ((bs k, 0) : EB × EF) + (((0 : EB), τ.mixedVectorField bs k x y') : EB × EF) := by
  refine (((hD.horizontalLiftField_apply _ (x, y')).trans
    (τ.horizontalLift_local bs hD hσ k y')).trans
    (Manifold.tangentSpaceProdEquiv_symm_apply _ _)).trans ?_
  exact Prod.ext (add_zero _).symm (zero_add _).symm

omit [CompleteSpace EB] [CompleteSpace EF] in
/-- On the fibre over `x`, `τ(∂ᵢ, ∂ⱼ) - τ(Lᵢ, Lⱼ) = σ(x)(Xᵢ, Xⱼ)`, where `Lₖ` is the horizontal
lift of the constant field `bs k`. -/
private theorem sub_val_horizontalLiftField_const (i j : ι) (y' : F) :
    τ.val (x, y') ![(bs i, 0), (bs j, 0)] -
        τ.val (x, y') ![hD.horizontalLiftField
            (fun _ ↦ bs i : Π b : EB, TangentSpace 𝓘(ℝ, EB) b) (x, y'),
          hD.horizontalLiftField (fun _ ↦ bs j : Π b : EB, TangentSpace 𝓘(ℝ, EB) b) (x, y')] =
      SmoothBundleForm.eval₂ (τ.smoothFiberComponent x) y'
        (τ.mixedVectorField bs i x y') (τ.mixedVectorField bs j x y') := by
  rw [horizontalLiftField_const_eq_add hD bs hσ i y',
    horizontalLiftField_const_eq_add hD bs hσ j y']
  set Xᵢ := τ.mixedVectorField bs i x y'
  set Xⱼ := τ.mixedVectorField bs j x y'
  -- The values of `τ` at `(x, y')`, on vectors of `EB × EF`.
  set T : (EB × EF) [⋀^Fin 2]→L[ℝ] ℝ := τ.val (x, y')
  have e₁ : SmoothBundleForm.eval₂ (τ.smoothFiberComponent x) y' Xᵢ Xⱼ =
      T ![(((0 : EB), Xⱼ) : EB × EF), (bs i, 0)] := by
    have h := τ.eval₂_mixedVectorField bs hσ i y' Xⱼ
    rw [RoughForm.mixedComponent_apply] at h
    exact h
  have e₂ : SmoothBundleForm.eval₂ (τ.smoothFiberComponent x) y' Xⱼ Xᵢ =
      T ![(((0 : EB), Xᵢ) : EB × EF), (bs j, 0)] := by
    have h := τ.eval₂_mixedVectorField bs hσ j y' Xᵢ
    rw [RoughForm.mixedComponent_apply] at h
    exact h
  have e₃ : SmoothBundleForm.eval₂ (τ.smoothFiberComponent x) y' Xᵢ Xⱼ =
      T ![(((0 : EB), Xᵢ) : EB × EF), ((0 : EB), Xⱼ)] :=
    τ.eval₂_smoothFiberComponent x y' Xᵢ Xⱼ
  have e₄ := SmoothBundleForm.eval₂_swap (τ.smoothFiberComponent x) y' Xⱼ Xᵢ
  have e₅ := T.apply_vecCons_swap (((0 : EB), Xⱼ) : EB × EF) ((bs i, 0) : EB × EF)
  have hexp (A a B b : EB × EF) : T ![A, B] - T ![A + a, B + b] =
      -(T ![A, b] + T ![a, B] + T ![a, b]) := by
    rw [T.vecCons_add, T.apply_vecCons_add_right, T.apply_vecCons_add_right]
    ring
  refine (hexp _ _ _ _).trans ?_
  linear_combination -e₅ - e₁ + e₂ - e₄ + e₃

omit [CompleteSpace EB] [CompleteSpace EF] in
/-- Where `τ` is vertically closed, `dτ(Lᵢ, Lⱼ, (0, w)) = dτ((bs i, 0), (bs j, 0), (0, w))`: the
lifts differ from the constant fields by vertical vectors, and `dτ` vanishes on two of them. -/
private theorem mextDeriv_horizontalLiftField_const {y : F}
    (hτ : RoughForm.IsVerticallyClosedOn 𝓘(ℝ, EB) Prod.fst τ.val {(x, y)}) (i j : ι)
    (w : TangentSpace IF y) :
    mextDeriv τ.val (x, y)
        ![hD.horizontalLiftField (fun _ ↦ bs i : Π b : EB, TangentSpace 𝓘(ℝ, EB) b) (x, y),
          hD.horizontalLiftField (fun _ ↦ bs j : Π b : EB, TangentSpace 𝓘(ℝ, EB) b) (x, y),
          ((0 : EB), w)] =
      mextDeriv τ.val (x, y) ![(bs i, 0), (bs j, 0), ((0 : EB), w)] := by
  set f : (EB × EF) [⋀^Fin 3]→L[ℝ] ℝ := mextDeriv τ.val (x, y)
  have hV (a b c : EB × EF) (ha : a.1 = 0) (hb : b.1 = 0) : f ![a, b, c] = 0 :=
    RoughForm.isVerticallyClosedOn_iff.1 hτ (x, y) rfl a (mem_ker_mfderiv_fst_iff.2 ha) b
      (mem_ker_mfderiv_fst_iff.2 hb) c
  have hsplit (A a B b c : EB × EF) (ha : a.1 = 0) (hb : b.1 = 0) (hc : c.1 = 0) :
      f ![A + a, B + b, c] = f ![A, B, c] := by
    rw [f.vecCons_add, f.map_vecCons_rotate a, f.map_vecCons_rotate A, f.vecCons_add,
      f.vecCons_add, hV b c A hb hc, hV b c a hb hc, f.map_vecCons_rotate B c a, hV c a B hc ha,
      f.map_vecCons_rotate B c A, f.map_vecCons_rotate c A B]
    simp
  rw [horizontalLiftField_const_eq_add hD bs hσ i y, horizontalLiftField_const_eq_add hD bs hσ j y]
  exact hsplit _ _ _ _ _ rfl rfl rfl

omit hσ [CompleteSpace EB] [CompleteSpace EF] [FiniteDimensional ℝ EF] in
/-- The function `τ((bs i, 0), (bs j, 0))` on `EB × F` is differentiable. -/
private theorem mdifferentiableAt_val_const (i j : ι) (y : F) :
    MDifferentiableAt (𝓘(ℝ, EB).prod IF) 𝓘(ℝ, ℝ)
      (fun z ↦ τ.val z ![(bs i, 0), (bs j, 0)]) (x, y) := by
  set A : ι → Π z : EB × F, TangentSpace (𝓘(ℝ, EB).prod IF) z := fun k ↦
    Manifold.prodVectorField (I := 𝓘(ℝ, EB)) (J := IF)
      (fun x ↦ (bs k : TangentSpace 𝓘(ℝ, EB) x)) (0 : (y : F) → TangentSpace IF y)
  have hA (k : ι) : MDifferentiableAt (𝓘(ℝ, EB).prod IF) (𝓘(ℝ, EB).prod IF).tangent
      (fun z ↦ (A k z : TangentBundle (𝓘(ℝ, EB).prod IF) (EB × F))) (x, y) :=
    Manifold.mdifferentiableAt_prodVectorField
      ((contMDiff_tangentBundle_mk_const (n := 1) _).mdifferentiableAt one_ne_zero)
      ((contMDiff_zeroSection ℝ (TangentSpace IF)).mdifferentiableAt one_ne_zero)
  have hAv (k : ι) (z : EB × F) : A k z = ((bs k, 0) : EB × EF) :=
    Manifold.prodVectorField_apply _ _ z
  have h := τ.mdifferentiableAt_apply_vectorField (V := ![A i, A j])
    (fun k ↦ by fin_cases k; exacts [hA i, hA j])
  have hev (z : EB × F) : (fun k ↦ ![A i, A j] k z) = ![A i z, A j z] := by
    funext k; fin_cases k <;> rfl
  simp only [hev, hAv] at h
  exact h

/-- **The curvature in a product chart.** Let `τ` be a smooth two-form on `EB × F` whose
`τ`-orthogonals of the vertical spaces of `Prod.fst` form a `C^n` Ehresmann connection `hD`,
`1 ≤ n`, and `bs` a basis of `EB`. Suppose that the fibre component `σ(x)` of `τ` over `x` is
nondegenerate and that `τ` is vertically closed at `(x, y)`. Then the curvature of the constant
fields `bs i`, `bs j` at `(x, y)` is vertical, and its component `V` along `F` satisfies, for every
tangent vector `w` of `F` at `y`,

`σ(x)(V, w) = ∂ᵢαⱼ(x)(w) - ∂ⱼαᵢ(x)(w) - d(σ(x)(Xᵢ(x), Xⱼ(x)))(w)`,

where `αₖ(x)` is the mixed component of `τ`, `∂ᵢ` differentiates in `x` along `bs i`, and
`Xₖ(x)` is the vector field on `F` with `ι(Xₖ(x)) σ(x) = αₖ(x)`. -/
theorem curvatureIn_local (hn : 1 ≤ n) {y : F}
    (hτ : RoughForm.IsVerticallyClosedOn 𝓘(ℝ, EB) Prod.fst τ.val {(x, y)}) (i j : ι) :
    (hD.curvature (fun _ ↦ bs i) (fun _ ↦ bs j) (x, y)).1 = 0 ∧
      ∀ w : TangentSpace IF y,
        SmoothBundleForm.eval₂ (τ.smoothFiberComponent x) y
            (hD.curvature (fun _ ↦ bs i) (fun _ ↦ bs j) (x, y)).2 w =
          fderiv ℝ (fun x' ↦ RoughForm.mixedComponent τ.val bs j x' y ![w]) x (bs i) -
            fderiv ℝ (fun x' ↦ RoughForm.mixedComponent τ.val bs i x' y ![w]) x (bs j) -
            mvfderiv IF (fun y' ↦ SmoothBundleForm.eval₂ (τ.smoothFiberComponent x) y'
              (τ.mixedVectorField bs i x y') (τ.mixedVectorField bs j x y')) y w := by
  have hc (k : ι) : ContMDiffAt 𝓘(ℝ, EB) 𝓘(ℝ, EB).tangent 1
      (fun b ↦ (⟨b, bs k⟩ : TangentBundle 𝓘(ℝ, EB) EB)) x :=
    (contMDiff_tangentBundle_mk_const _).contMDiffAt
  have hproj : ContMDiff (𝓘(ℝ, EB).prod IF) 𝓘(ℝ, EB) 2 (Prod.fst : EB × F → EB) := contMDiff_fst
  have hver := hD.curvature_mem_ker hn (hproj (x, y)) (hc i) (hc j)
  rw [mem_ker_mfderiv_fst_iff] at hver
  refine ⟨hver, fun w ↦ ?_⟩
  set Ω := hD.curvature (fun _ ↦ bs i) (fun _ ↦ bs j) (x, y)
  set Lᵢ := hD.horizontalLiftField (fun _ ↦ bs i : Π b : EB, TangentSpace 𝓘(ℝ, EB) b)
  set Lⱼ := hD.horizontalLiftField (fun _ ↦ bs j : Π b : EB, TangentSpace 𝓘(ℝ, EB) b)
  -- The curvature identity along the vertical vector `(0, w)`.
  have hη : (((0 : EB), w) : TangentSpace (𝓘(ℝ, EB).prod IF) (x, y)) ∈
      (mfderiv (𝓘(ℝ, EB).prod IF) 𝓘(ℝ, EB) Prod.fst (x, y)).ker :=
    mem_ker_mfderiv_fst_iff.2 rfl
  have hid := apply_curvature_eq_mvfderiv_sub_mextDeriv hD hn hproj (hc i) (hc j) hη
  -- Its left side: the curvature is vertical, so `τ` pairs it with `(0, w)` through `σ(x)`.
  have hlhs : τ.val (x, y) ![Ω, ((0 : EB), w)] =
      SmoothBundleForm.eval₂ (τ.smoothFiberComponent x) y Ω.2 w := by
    refine (congrArg (fun v ↦ τ.val (x, y) ![v, ((0 : EB), w)]) (Prod.ext hver rfl :
      Ω = ((0 : EB), Ω.2))).trans ?_
    exact (τ.eval₂_smoothFiberComponent x y _ w).symm
  -- `dτ` on the constant fields and `(0, w)`, by Tau Ceti's formula on a parameter product.
  have hdτ := mextDeriv_horizontalLiftField_const hD bs hσ hτ i j w
  have hfAB := SmoothForm.mextDeriv_apply_eq_fderiv_sub_fderiv_add_mvfderiv τ x y (bs i) (bs j) w
  have ha (k : ι) (v : EB) : fderiv ℝ (fun q ↦ τ.val (q, y) ![(bs k, 0), ((0 : EB), w)]) x v =
      -fderiv ℝ (fun x' ↦ RoughForm.mixedComponent τ.val bs k x' y ![w]) x v := by
    have hα : (fun q ↦ τ.val (q, y) ![(bs k, 0), ((0 : EB), w)]) =
        fun q ↦ -RoughForm.mixedComponent τ.val bs k q y ![w] :=
      funext fun q ↦ by
        rw [RoughForm.mixedComponent_apply]
        exact (τ.val (q, y)).apply_vecCons_swap _ _
    have h := congrArg (fun φ ↦ fderiv ℝ φ x v) hα
    simp only [fderiv_fun_neg] at h
    exact h
  -- The derivative along `(0, w)` of `τ(Lᵢ, Lⱼ)` is read on the fibre over `x`.
  have hfd := mdifferentiableAt_val_const (τ := τ) bs (x := x) i j y
  have hg : MDifferentiableAt (𝓘(ℝ, EB).prod IF) 𝓘(ℝ, ℝ) (fun z ↦ τ.val z ![Lᵢ z, Lⱼ z])
      (x, y) := by
    have hL (k : ι) := hD.mdifferentiableAt_horizontalLiftField hn (hproj (x, y))
      (V := (fun _ ↦ bs k : Π b : EB, TangentSpace 𝓘(ℝ, EB) b)) (hc k)
    have hev (z : EB × F) : (fun k ↦ ![Lᵢ, Lⱼ] k z) = ![Lᵢ z, Lⱼ z] := by
      funext k; fin_cases k <;> rfl
    simpa [hev] using τ.mdifferentiableAt_apply_vectorField (V := ![Lᵢ, Lⱼ])
      (fun k ↦ by fin_cases k; exacts [hL i, hL j])
  have hS : mvfderiv IF (fun y' ↦ SmoothBundleForm.eval₂ (τ.smoothFiberComponent x) y'
        (τ.mixedVectorField bs i x y') (τ.mixedVectorField bs j x y')) y w =
      mvfderiv IF (fun y' ↦ τ.val (x, y') ![(bs i, 0), (bs j, 0)]) y w -
        mvfderiv (𝓘(ℝ, EB).prod IF) (fun z ↦ τ.val z ![Lᵢ z, Lⱼ z]) (x, y) ((0 : EB), w) := by
    have hmk : MDifferentiableAt IF (𝓘(ℝ, EB).prod IF) (fun y' : F ↦ (x, y')) y :=
      mdifferentiableAt_const.prodMk mdifferentiableAt_id
    have h := congrArg (fun L ↦ L w) (mvfderiv_fun_sub (hfd.comp y hmk) (hg.comp y hmk))
    simp only [sub_apply] at h
    rw [hg.mvfderiv_prod_eq_apply_of_fst_eq_zero
      (v := (((0 : EB), w) : TangentSpace (𝓘(ℝ, EB).prod IF) (x, y))) rfl]
    exact (congrArg (fun φ ↦ mvfderiv IF φ y w)
      (funext fun y' ↦ (sub_val_horizontalLiftField_const hD bs hσ i j y').symm)).trans h
  linear_combination -hlhs + hid - hdτ - hfAB - ha j (bs i) + ha i (bs j) + hS

end Local

end TauCeti.IsEhresmannConnection
