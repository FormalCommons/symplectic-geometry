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
import SymplecticGeometry.Geometry.Manifold.Submersion.VerticalProjection
import SymplecticGeometry.Geometry.Manifold.VectorField.Chart
import TauCeti.Geometry.Manifold.Distribution.Kernel
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
import TauCeti.Geometry.Manifold.IsManifold.Basic

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
When `τ` is closed and restricts to `σ` on the fibres of a smooth atlas, its connection has
Hamiltonian curvature: by the identity above, the curvature read in a chart is a Hamiltonian
vector field of the function `τ(v₁♯, v₂♯)` read on the fibre through the chart
([GuilleminLermanSternberg1996], equation (1.12)).
This is the curvature condition of McDuff–Salamon [McDuffSalamon2017], Exercise 6.4.9, and of
[GuilleminLermanSternberg1996], §1.4.

Finally, the file computes the curvature read in a chart `e` of a smooth atlas over a coordinate
patch of a base without boundary. With `φ` the extended chart of `B` at `b`, the map
`Φ p = (φ (proj p), (e p).2)` identifies a neighbourhood of the fibre over `b` with an open set
of `EB × F`. If a two-form `τ'` there pulls back by `Φ` to `τ` near a point, then `dΦ` carries
the connection of `τ` into that of `τ'` near that point
(`TauCeti.SmoothTwoForm.map_mfderiv_horizontalDistribution`), so by the naturality of the curvature
(`TauCeti.IsEhresmannConnection.mfderiv_curvature_of_related`) the curvature of `v₁ v₂` is carried
to that of their push-forwards by `φ`. On `EB` these push-forwards are combinations of constant
fields, and the curvature expands bilinearly
(`TauCeti.IsEhresmannConnection.curvature_eq_sum_basis`). The fibre component of the result is
the curvature read in `e`.

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
* `TauCeti.IsEhresmannConnection.isHamiltonianVectorField_curvatureIn_of_isClosed`: for a closed
  two-form that restricts to `σ` on the fibres, the curvature read in a chart is a Hamiltonian
  vector field of `τ(v₁♯, v₂♯)` read on the fibre.
* `TauCeti.IsEhresmannConnection.hasHamiltonianCurvature_of_isClosed`: the connection of a closed
  two-form that restricts to `σ` on the fibres has Hamiltonian curvature.
* `TauCeti.IsEhresmannConnection.curvatureIn_eq_snd_sum_curvature`: the curvature read in a chart
  over a coordinate patch, in terms of the curvature of a two-form on `EB × F` on constant fields.

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

/-! ### Closed two-forms -/

section Closed

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [CompleteSpace EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B] [IsManifold IB 2 B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  [IsManifold IF ∞ F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [CompleteSpace EM] {HM : Type*}
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M]
  [ChartedSpace HM M] [IsManifold IM ∞ M]
  {proj : M → B} {τ : SmoothTwoForm IM M} {n : ℕ∞ω}

attribute [local instance] IsManifold.minSmoothness_of_isRCLikeNormedField

/-- **The Hamiltonian of the curvature of a closed form.** Let `A` be a smooth atlas of `proj`
with fibre `F`, `τ` a closed two-form on `M` that restricts to `σ` on the fibres of `A`, and `hD`
the connection of `τ`, a `C^n` Ehresmann connection with `1 ≤ n`. For a chart `e` of `A`, a point
`b` of its base set and fields `v₁ v₂` on `B` that are `C^1` at `b`, the curvature on the fibre
over `b` read in `e` is a Hamiltonian vector field, in Tau Ceti's sign (`ι_X σ = df`), of the
function `y ↦ τ(v₁♯, v₂♯)` at `e⁻¹ (b, y)` ([GuilleminLermanSternberg1996], equation (1.12)). -/
theorem isHamiltonianVectorField_curvatureIn_of_isClosed
    (hD : IsEhresmannConnection IM IB n proj (SmoothTwoForm.horizontalDistribution IB proj τ))
    (hn : 1 ≤ n) {A : MapFiber.Atlas F proj} (hA : A.IsContMDiff ∞ IB IF IM)
    {σ : SmoothTwoForm IF F} (hτ : τ.IsClosed) (hτσ : A.RestrictsTo σ τ) {b' b : B}
    (hb : b ∈ (A.trivAt b').baseSet) {v₁ v₂ : Π b : B, TangentSpace IB b}
    (hv₁ : ContMDiffAt IB IB.tangent 1 (T% v₁) b) (hv₂ : ContMDiffAt IB IB.tangent 1 (T% v₂) b) :
    σ.IsHamiltonianVectorField
      (fun y ↦ τ.val ((A.trivAt b').fiberInclusionMap hb y)
        ![hD.horizontalLiftField v₁ ((A.trivAt b').fiberInclusionMap hb y),
          hD.horizontalLiftField v₂ ((A.trivAt b').fiberInclusionMap hb y)])
      (hD.curvatureIn IF (A.trivAt b') b v₁ v₂) := by
  have hproj : ContMDiff IM IB ∞ proj := hA.contMDiff_proj
  have he := hA.mdifferentiable_trivAt (by simp) b'
  have hi : ContMDiff IF IM ∞ ((A.trivAt b').fiberInclusionMap hb) :=
    (A.trivAt b').contMDiff_fiberInclusionMap (hA.contMDiffOn_trivAt_symm b') hb
  refine SmoothTwoForm.isHamiltonianVectorField_iff.2 fun y w ↦ ?_
  have hpy : proj ((A.trivAt b').fiberInclusionMap hb y) = b :=
    (A.trivAt b').proj_fiberInclusionMap hb y
  have hv₁x : ContMDiffAt IB IB.tangent 1 (T% v₁) (proj ((A.trivAt b').fiberInclusionMap hb y)) :=
    by rwa [hpy]
  have hv₂x : ContMDiffAt IB IB.tangent 1 (T% v₂) (proj ((A.trivAt b').fiberInclusionMap hb y)) :=
    by rwa [hpy]
  have hproj₂ : ContMDiffAt IM IB 2 proj ((A.trivAt b').fiberInclusionMap hb y) :=
    (hproj _).of_le (by simp)
  -- The function `τ(v₁♯, v₂♯)` is differentiable at the point, the lifts being so.
  have hg : MDifferentiableAt IM 𝓘(ℝ)
      (fun x ↦ τ.val x ![hD.horizontalLiftField v₁ x, hD.horizontalLiftField v₂ x])
      ((A.trivAt b').fiberInclusionMap hb y) := by
    convert SmoothForm.mdifferentiableAt_apply_vectorField τ
      (V := ![hD.horizontalLiftField v₁, hD.horizontalLiftField v₂]) fun i ↦ by
        fin_cases i
        · exact hD.mdifferentiableAt_horizontalLiftField hn hproj₂ hv₁x
        · exact hD.mdifferentiableAt_horizontalLiftField hn hproj₂ hv₂x using 3 with x
    ext i
    fin_cases i <;> rfl
  -- The curvature read in the chart is carried back to the curvature by the fibre inclusion.
  have hΩ : mfderiv IF IM ((A.trivAt b').fiberInclusionMap hb) y
      (hD.curvatureIn IF (A.trivAt b') b v₁ v₂ y) =
        hD.curvature v₁ v₂ ((A.trivAt b').fiberInclusionMap hb y) := by
    rw [curvatureIn_def, ← (A.trivAt b').fiberInclusionMap_apply hb]
    exact (A.trivAt b').mfderiv_fiberInclusionMap_mfderiv_snd_apply he hb y
      (hD.curvature_mem_ker hn hproj₂ hv₁x hv₂x)
  have hid := apply_curvature_eq_mvfderiv_sub_mextDeriv hD hn (hproj.of_le (by simp)) hv₁x hv₂x
    ((A.trivAt b').mfderiv_proj_mfderiv_fiberInclusionMap_apply (IM := IM) (IB := IB) hb y w)
  rw [(SmoothForm.isClosed_def τ).1 hτ] at hid
  simp only [Pi.zero_apply, ContinuousAlternatingMap.coe_zero, sub_zero] at hid
  have hc := mvfderiv_comp_apply y hg ((hi y).mdifferentiableAt (by simp)) w
  rw [Function.comp_def] at hc
  rw [SmoothBundleForm.eval₂_apply, ← MapFiber.Atlas.restrictsTo_iff.1 hτσ b' b hb,
    TauCeti.mpullback_apply_pair (I := IF) (I' := IM), hΩ, hid, hc]

/-- **Closed forms have Hamiltonian curvature.** Let `A` be a smooth atlas of `proj` with fibre
`F`, `τ` a closed two-form on `M` that restricts to `σ` on the fibres of `A`, and `hD` the
connection of `τ`, a `C^n` Ehresmann connection with `∞ ≤ n`. Then `hD` has Hamiltonian curvature
for `A` and `σ`; the Hamiltonians are those of
`TauCeti.IsEhresmannConnection.isHamiltonianVectorField_curvatureIn_of_isClosed`. -/
theorem hasHamiltonianCurvature_of_isClosed
    (hD : IsEhresmannConnection IM IB n proj (SmoothTwoForm.horizontalDistribution IB proj τ))
    (hn : ∞ ≤ n) {A : MapFiber.Atlas F proj} (hA : A.IsContMDiff ∞ IB IF IM)
    {σ : SmoothTwoForm IF F} (hτ : τ.IsClosed) (hτσ : A.RestrictsTo σ τ) :
    hD.HasHamiltonianCurvature A σ := by
  intro b' b hb v₁ v₂ hv₁ hv₂
  have hproj : ContMDiff IM IB ∞ proj := hA.contMDiff_proj
  -- The lifts of smooth fields are smooth, the connection being smooth.
  have hL {v : Π b : B, TangentSpace IB b} (hv : ContMDiff IB IB.tangent ∞ (T% v)) :
      ContMDiff IM IM.tangent ∞ (T% (hD.horizontalLiftField v)) := by
    rw [← hD.horizontalLiftField_of_le v hn]
    exact (hD.of_le hn).contMDiff_horizontalLiftField (by simpa using hproj) hv
  have hg : ContMDiff IM 𝓘(ℝ) ∞
      (fun x ↦ τ.val x ![hD.horizontalLiftField v₁ x, hD.horizontalLiftField v₂ x]) := by
    simpa using τ.contMDiff_apply (b := id) (hL hv₁) (hL hv₂)
  exact ⟨_, hg.comp ((A.trivAt b').contMDiff_fiberInclusionMap (hA.contMDiffOn_trivAt_symm b') hb),
    hD.isHamiltonianVectorField_curvatureIn_of_isClosed (le_trans (by simp) hn) hA hτ hτσ hb
      ((hv₁ b).of_le (by simp)) ((hv₂ b).of_le (by simp))⟩

end Closed

/-! ### The curvature read in a chart over a coordinate patch -/

section ChartReading

open Set
open scoped Topology

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [CompleteSpace EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless] {B : Type*}
  [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB 2 B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [CompleteSpace EF] {HF : Type*}
  [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F]
  [ChartedSpace HF F] [IsManifold IF ∞ F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [CompleteSpace EM] {HM : Type*}
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M]
  [ChartedSpace HM M] [IsManifold IM ∞ M]
  {proj : M → B} {A : MapFiber.Atlas F proj}

attribute [local instance] IsManifold.minSmoothness_of_isRCLikeNormedField

/-- **The curvature read in a chart over a coordinate patch.** Let `A` be a smooth atlas of
`proj : M → B` with fibre `F`, over a base without boundary, and `hD` the connection of a
two-form `τ` on `M`, a `C^n` Ehresmann connection with `1 ≤ n`. Take a chart `e = A.trivAt b'`,
a point `b` of its base set, the extended chart `φ` of `B` at `b`, and the map
`Φ p = (φ (proj p), (e p).2)` to `EB × F`. Let `τ'` be a two-form on `EB × F` whose connection
`hD'` for `Prod.fst` is a `C^n'` Ehresmann connection with `1 ≤ n'`, and whose pull-back by `Φ`
equals `τ` near `x = e⁻¹ (b, y)`. Then for vector fields `v₁ v₂` on `B` that are `C^1` at `b`
and a basis `bs` of `EB`, the curvature on the fibre over `b` read in `e`, at `y`, is the fibre
component of `∑ i, ∑ j, cᵢ dⱼ • Ω'(bs i, bs j)` at `(φ b, y)`, where `Ω'(bs i, bs j)` is the
curvature of `hD'` on the constant fields `bs i`, `bs j`, and `c`, `d` are the coordinates in
`bs` of `dφ (v₁ b)` and `dφ (v₂ b)`. -/
theorem curvatureIn_eq_snd_sum_curvature
    {τ : SmoothTwoForm IM M} {n : ℕ∞ω}
    (hD : IsEhresmannConnection IM IB n proj (SmoothTwoForm.horizontalDistribution IB proj τ))
    (hn : 1 ≤ n) (hA : A.IsContMDiff ∞ IB IF IM) {b' b : B} (hb : b ∈ (A.trivAt b').baseSet)
    {τ' : SmoothTwoForm (𝓘(ℝ, EB).prod IF) (EB × F)} {n' : ℕ∞ω}
    (hD' : IsEhresmannConnection (𝓘(ℝ, EB).prod IF) 𝓘(ℝ, EB) n' Prod.fst
      (SmoothTwoForm.horizontalDistribution 𝓘(ℝ, EB) Prod.fst τ')) (hn' : 1 ≤ n') {y : F}
    (hτ' : ∀ᶠ p in 𝓝 ((A.trivAt b').toOpenPartialHomeomorph.symm (b, y)),
      mpullback IM (𝓘(ℝ, EB).prod IF) (fun p ↦ (extChartAt IB b (proj p), (A.trivAt b' p).2))
        τ'.val p = τ.val p)
    {ι : Type*} [Fintype ι] (bs : Module.Basis ι ℝ EB) {v₁ v₂ : Π b : B, TangentSpace IB b}
    (hv₁ : ContMDiffAt IB IB.tangent 1 (T% v₁) b) (hv₂ : ContMDiffAt IB IB.tangent 1 (T% v₂) b) :
    hD.curvatureIn IF (A.trivAt b') b v₁ v₂ y =
      (∑ i, ∑ j, (bs.repr (mfderiv IB 𝓘(ℝ, EB) (extChartAt IB b) b (v₁ b)) i *
          bs.repr (mfderiv IB 𝓘(ℝ, EB) (extChartAt IB b) b (v₂ b)) j) •
        hD'.curvature (fun _ ↦ bs i) (fun _ ↦ bs j) (extChartAt IB b b, y)).2 := by
  set e := A.trivAt b'
  set Φ : M → EB × F := fun p ↦ (extChartAt IB b (proj p), (e p).2) with hΦdef
  set x := e.toOpenPartialHomeomorph.symm (b, y)
  have hpx : proj x = b := e.proj_symm_apply' hb
  have hex : e x = (b, y) := e.apply_symm_apply' hb
  have hxe : x ∈ e.source := e.mem_source.2 (by rw [hpx]; exact hb)
  have hΦx : Φ x = (extChartAt IB b b, y) := by simp only [hΦdef, hpx, hex]
  have hproj : ContMDiff IM IB ∞ proj := hA.contMDiff_proj
  -- The points over which `Φ` is a chart.
  have hU : e.source ∩ proj ⁻¹' (chartAt HB b).source ∈ 𝓝 x :=
    inter_mem (e.open_source.mem_nhds hxe) ((hproj.continuous.continuousAt).preimage_mem_nhds
      ((chartAt HB b).open_source.mem_nhds (by rw [hpx]; exact mem_chart_source HB b)))
  have hΦ (z : M) (hz : z ∈ e.source ∩ proj ⁻¹' (chartAt HB b).source) :
      ContMDiffAt IM (𝓘(ℝ, EB).prod IF) 2 Φ z ∧
        Function.Surjective (mfderiv IM (𝓘(ℝ, EB).prod IF) Φ z) :=
    ⟨hA.contMDiffAt_extChartAt_proj_prodMk_snd (by simp) (e.mem_source.1 hz.1) hz.2,
      hA.surjective_mfderiv_extChartAt_proj_prodMk_snd (by simp) (e.mem_source.1 hz.1) hz.2⟩
  -- `dΦ` carries the connection of `τ` into that of `τ'` near `x`.
  have hΦD : ∀ᶠ z in 𝓝 x, ∀ w ∈ SmoothTwoForm.horizontalDistribution IB proj τ z,
      mfderiv IM (𝓘(ℝ, EB).prod IF) Φ z w ∈
        SmoothTwoForm.horizontalDistribution 𝓘(ℝ, EB) Prod.fst τ' (Φ z) := by
    filter_upwards [hU, hτ'] with z hz hτz w hw
    have hzb : proj z ∈ (extChartAt IB b).source := by rw [extChartAt_source]; exact hz.2
    rw [← SmoothTwoForm.map_mfderiv_horizontalDistribution (proj := proj) (proj' := Prod.fst)
      (ψ := extChartAt IB b) (Φ := Φ) (τ := τ) (τ' := τ') EventuallyEq.rfl
      ((hproj z).mdifferentiableAt (by simp)) (((hΦ z hz).1).mdifferentiableAt two_ne_zero)
      ((contMDiffAt_extChartAt' (n := 2) hz.2).mdifferentiableAt two_ne_zero)
      mdifferentiableAt_fst (isInvertible_mfderiv_extChartAt hzb).injective (hΦ z hz).2 hτz]
    exact Submodule.mem_map_of_mem hw
  -- The fields on `EB` that `φ` relates `v₁ v₂` to.
  have hrel {v : Π b : B, TangentSpace IB b} :
      ∀ᶠ c in 𝓝 (proj x), mfderiv IB 𝓘(ℝ, EB) (extChartAt IB b) c (v c) =
        VectorField.mpullback 𝓘(ℝ, EB) IB (extChartAt IB b).symm v
          (extChartAt IB b c) := by
    rw [hpx]
    have h := eventuallyEq_mpullback_mpullbackWithin_extChartAt (s := univ) (x := b) v
    rw [nhdsWithin_univ, IB.range_eq_univ, VectorField.mpullbackWithin_univ] at h
    filter_upwards [h, extChartAt_source_mem_nhds (I := IB) b] with c hc hcs
    rw [hc, VectorField.mpullback_apply, (isInvertible_mfderiv_extChartAt hcs).self_apply_inverse]
  have hreg {v : Π b : B, TangentSpace IB b} (hv : ContMDiffAt IB IB.tangent 1 (T% v) b) :
      ContMDiffAt 𝓘(ℝ, EB) 𝓘(ℝ, EB).tangent 1
        (T% (VectorField.mpullback 𝓘(ℝ, EB) IB (extChartAt IB b).symm v))
        (Prod.fst (Φ x)) := by
    rw [hΦx]
    exact contMDiffAt_vectorSpace_iff_contDiffAt.2
      (ContMDiffAt.contDiffAt_mpullback_extChartAt_symm hv)
  have hcurv := hD.mfderiv_curvature_of_related hD' hn hn' ((hproj x).of_le (by simp))
    contMDiffAt_fst (hΦ x (mem_of_mem_nhds hU)).1
    (contMDiffAt_extChartAt' (n := 2) (by rw [hpx]; exact mem_chart_source HB b))
    EventuallyEq.rfl hΦD (by rw [hpx]; exact hv₁) (by rw [hpx]; exact hv₂) (hreg hv₁) (hreg hv₂)
    hrel hrel
  -- The curvature read in `e` is the fibre component of `dΦ` applied to the curvature.
  have hsnd : hD.curvatureIn IF e b v₁ v₂ y =
      (mfderiv IM (𝓘(ℝ, EB).prod IF) Φ x (hD.curvature v₁ v₂ x)).2 := by
    rw [curvatureIn_def, hΦdef, mfderiv_prodMk (f := fun p ↦ extChartAt IB b (proj p))
      (g := fun p ↦ (e p).2)
      ((contMDiffAt_extChartAt' (n := 2) (by rw [hpx]; exact mem_chart_source HB b)).comp x
        ((hproj x).of_le (by simp)) |>.mdifferentiableAt two_ne_zero)
      ((hA.contMDiffAt_snd_trivAt (e.mem_source.1 hxe)).mdifferentiableAt (by simp))]
    -- `ContinuousLinearMap.prod_apply` does not match here, the tangent spaces of `EB × F` being
    -- products only by definition.
    rfl
  have h₁ := (hrel (v := v₁)).self_of_nhds
  have h₂ := (hrel (v := v₂)).self_of_nhds
  rw [hpx] at h₁ h₂
  rw [hsnd, hcurv, hD'.curvature_eq_sum_basis hn' contMDiffAt_fst bs (hreg hv₁) (hreg hv₂), hΦx,
    h₁, h₂]

end ChartReading

end TauCeti.IsEhresmannConnection
