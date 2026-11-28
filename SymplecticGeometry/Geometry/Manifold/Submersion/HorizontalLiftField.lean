/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Submersion.EhresmannConnection.Basic
import TauCeti.Analysis.Normed.Module.ContinuousInverse
import TauCeti.Geometry.Manifold.ContMDiff.LeftInverse
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity
import TauCeti.Topology.VectorBundle.Trivialization
import SymplecticGeometry.Geometry.Manifold.IsManifold.Basic
import SymplecticGeometry.Topology.FiberBundle.Basic

/-!
# Horizontal lifts of vector fields

Let `D` be an Ehresmann connection on a map `f : P → B` (Tau Ceti's
`TauCeti.IsEhresmannConnection`). Lifting the value of a vector field `V` on `B` at `f x`
horizontally at every point `x` of `P` gives a vector field on `P`, the horizontal lift of `V`.
It is horizontal, projects to `V` under the derivative of `f`, and depends linearly on `V`, over
the functions on `B` pulled back by `f`.

Over `ℝ` or `ℂ`, the lift is as smooth as the connection: for a `C^n` connection on a `C^(n+1)`
map, the horizontal lift at `g q` of a tangent vector `w q` of the base is `C^n` in `q` when `g`
and `w` are (`TauCeti.IsEhresmannConnection.contMDiffAt_horizontalLift`). Near a point, take a
`C^n` frame `X` of `D`. Its images under `df`, read in a trivialization of the tangent bundle of
`B`, form a `C^n` family of injective linear maps `A`, which have `C^n` left inverses `L`
(`ContMDiffAt.exists_contMDiffAt_leftInverse`); the coefficients of the lift of `w q` in the
frame are `L q` applied to `w q` read in that trivialization. This follows the proof of Tau Ceti's
`TauCeti.IsDistributionFrameOn.exists_mdifferentiableAt_coeff`, where the coefficients of a field
in a frame are recovered in the same way.

For a Riemannian submersion, Tau Ceti lifts tangent vectors through the metric adjoint of the
derivative (`TauCeti.IsRiemannianSubmersion.horizontalLift`). That lift is the horizontal lift
of the Ehresmann connection formed by the orthogonal complements of the vertical spaces
(`TauCeti.IsRiemannianSubmersion.horizontalLift_eq_isEhresmannConnection_horizontalLift`, in
Tau Ceti's `TauCeti.Geometry.Manifold.Riemannian.Submersion.Ehresmann`), so results about
general connections apply to it.

The horizontal lift at a point only sees the horizontal space there and the value of the field
below it, so it is local: two connections that agree near `x` lift fields that agree near `f x`
to fields that agree near `x`. It is also natural. Let `Φ : P → P'` cover `ψ : B → B'` near `x`,
so that `f' ∘ Φ = ψ ∘ f` near `x`, with derivative carrying `D` into the horizontal spaces `D'`
of a connection on `f'`. Then `dΦ` maps the lift of `v (f x)` at `x` to the lift at `Φ x` of its
image under `dψ`, since that image is horizontal and projects correctly; this is the argument of
Tau Ceti's `TauCeti.IsEhresmannConnectionHom.mfderiv_horizontalLift`, here for maps that cover
each other only near a point, such as maps defined on a coordinate patch. So lifts of
`ψ`-related fields are `Φ`-related. No invertibility of `Φ` or `ψ` is needed.

## Main definitions

* `TauCeti.IsEhresmannConnection.horizontalLiftField`: the horizontal lift of a vector field on
  the base.

## Main results

* `TauCeti.IsEhresmannConnection.of_le`: a `C^n` connection is a `C^m` one for `m ≤ n`.
* `TauCeti.IsEhresmannConnection.horizontalLiftField_mem` and
  `TauCeti.IsEhresmannConnection.mfderiv_horizontalLiftField`: the lift is horizontal and
  projects to the field on the base; `TauCeti.IsEhresmannConnection.eq_horizontalLiftField_iff`
  characterizes it by these two properties.
* `TauCeti.IsEhresmannConnection.horizontalLiftField_add` and
  `TauCeti.IsEhresmannConnection.horizontalLiftField_smul`: the lift is additive, and linear over
  functions on the base.
* `TauCeti.IsEhresmannConnection.horizontalLiftField_apply_eq_of_eq` and
  `TauCeti.IsEhresmannConnection.horizontalLiftField_eventuallyEq`: horizontal lifts are local
  in the connection and in the field.
* `TauCeti.IsEhresmannConnection.mfderiv_horizontalLiftField_eq_of_related` and
  `TauCeti.IsEhresmannConnection.eventually_mfderiv_horizontalLiftField_eq_of_related`: a map
  covering another and carrying one connection into the other relates the horizontal lifts of
  related fields.
* `TauCeti.IsEhresmannConnection.contMDiffAt_horizontalLift` and
  `TauCeti.IsEhresmannConnection.contMDiff_horizontalLift`: horizontal lifts of tangent vectors
  depend smoothly on their base point and on the vector.
* `TauCeti.IsEhresmannConnection.contMDiff_horizontalLiftField` and
  `TauCeti.IsEhresmannConnection.contMDiff_horizontalLiftField_family`: the horizontal
  lift of a smooth vector field, or of a smooth family of them indexed by a manifold, such as a
  time-dependent field, jointly in the parameter and the point, is smooth.
* `TauCeti.IsEhresmannConnection.isDistributionFrameOn_horizontalLiftField`: the lifts of a local
  frame of the tangent bundle of the base form a local frame of the connection.
* `TauCeti.IsEhresmannConnection.contMDiffAt_one_horizontalLiftField` and
  `TauCeti.IsEhresmannConnection.mdifferentiableAt_horizontalLiftField`: for a `C^n` connection
  with `1 ≤ n`, the horizontal lift of a `C^1` field is `C^1`, so differentiable, where `f` is
  `C^2`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.3.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §9.
-/

public section

noncomputable section

open Function Bundle Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace IsEhresmannConnection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I 1 P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {B : Type*} [TopologicalSpace B] [ChartedSpace G B]
  {n : ℕ∞ω} {f : P → B} {D : Π x : P, Submodule 𝕜 (TangentSpace I x)}
  (hD : IsEhresmannConnection I J n f D)

include hD in
/-- A `C^n` Ehresmann connection is a `C^m` Ehresmann connection for every `m ≤ n`. -/
theorem of_le {m : ℕ∞ω} (hmn : m ≤ n) : IsEhresmannConnection I J m f D :=
  ⟨hD.mdifferentiable, hD.isCompl_ker, hD.surjective_mfderiv,
    hD.isContMDiffDistribution.of_le hmn⟩

/-- The horizontal lift at a point does not depend on the smoothness index at which the
connection is seen. -/
theorem horizontalLift_of_le {m : ℕ∞ω} (hmn : m ≤ n) (x : P) :
    (hD.of_le hmn).horizontalLift x = hD.horizontalLift x :=
  LinearEquiv.ext fun v ↦ hD.eq_horizontalLift_iff.2 ((hD.of_le hmn).mfderiv_horizontalLift x v)

/-- Given an Ehresmann connection `D` on `f : P → B` and a field `V` on the base `B`, the
**horizontal lift** of `V` is the field on `P` whose value at `x` is the horizontal lift to `D x`
of `V (f x)`. -/
def horizontalLiftField (V : Π b : B, TangentSpace J b) : Π x : P, TangentSpace I x :=
  fun x ↦ (hD.horizontalLift x (V (f x)) : TangentSpace I x)

variable (V W : Π b : B, TangentSpace J b)

theorem horizontalLiftField_def :
    hD.horizontalLiftField V = fun x ↦ (hD.horizontalLift x (V (f x)) : TangentSpace I x) :=
  (rfl)

@[simp]
theorem horizontalLiftField_apply (x : P) :
    hD.horizontalLiftField V x = hD.horizontalLift x (V (f x)) :=
  (rfl)

/-- The horizontal lift of a vector field is horizontal. -/
theorem horizontalLiftField_mem (x : P) : hD.horizontalLiftField V x ∈ D x := by
  rw [horizontalLiftField_apply]
  exact (hD.horizontalLift x (V (f x))).property

/-- The derivative of `f` maps the horizontal lift of `V` at `x` to `V (f x)`. -/
theorem mfderiv_horizontalLiftField (x : P) :
    mfderiv I J f x (hD.horizontalLiftField V x) = V (f x) := by
  rw [horizontalLiftField_apply, mfderiv_horizontalLift]

/-- The horizontal lift of `V` is the only vector field on `P` that is horizontal and is mapped
to `V` by the derivative of `f`. -/
theorem eq_horizontalLiftField_iff {X : Π x : P, TangentSpace I x} :
    X = hD.horizontalLiftField V ↔ ∀ x, X x ∈ D x ∧ mfderiv I J f x (X x) = V (f x) := by
  refine ⟨fun h ↦ h ▸ fun x ↦ ⟨hD.horizontalLiftField_mem V x,
    hD.mfderiv_horizontalLiftField V x⟩, fun h ↦ funext fun x ↦ ?_⟩
  rw [horizontalLiftField_apply]
  exact congrArg Subtype.val
    ((hD.eq_horizontalLift_iff (w := ⟨X x, (h x).1⟩)).2 (h x).2)

/-- The horizontal lift does not depend on the smoothness index at which the connection is
seen. -/
theorem horizontalLiftField_of_le {m : ℕ∞ω} (hmn : m ≤ n) :
    (hD.of_le hmn).horizontalLiftField V = hD.horizontalLiftField V :=
  (hD.eq_horizontalLiftField_iff V).2 fun x ↦
    ⟨(hD.of_le hmn).horizontalLiftField_mem V x, (hD.of_le hmn).mfderiv_horizontalLiftField V x⟩

/-- The horizontal lift of `V` vanishes at the points `x` where `V (f x)` vanishes. -/
theorem horizontalLiftField_eq_zero {x : P} (hx : V (f x) = 0) :
    hD.horizontalLiftField V x = 0 := by
  rw [horizontalLiftField_apply, hx, map_zero, Submodule.coe_zero]

@[simp]
theorem horizontalLiftField_zero : hD.horizontalLiftField (0 : Π b : B, TangentSpace J b) = 0 :=
  funext fun _ ↦ hD.horizontalLiftField_eq_zero _ rfl

theorem horizontalLiftField_add :
    hD.horizontalLiftField (V + W) = hD.horizontalLiftField V + hD.horizontalLiftField W :=
  funext fun x ↦ by
    simp only [horizontalLiftField_apply, Pi.add_apply, map_add, Submodule.coe_add]

theorem horizontalLiftField_neg : hD.horizontalLiftField (-V) = -hD.horizontalLiftField V :=
  funext fun x ↦ by
    simp only [horizontalLiftField_apply, Pi.neg_apply, map_neg, Submodule.coe_neg]

theorem horizontalLiftField_sub :
    hD.horizontalLiftField (V - W) = hD.horizontalLiftField V - hD.horizontalLiftField W :=
  funext fun x ↦ by
    simp only [horizontalLiftField_apply, Pi.sub_apply, map_sub, Submodule.coe_sub]

/-- The horizontal lift is linear over functions on the base: lifting `g • V` multiplies the
lift of `V` by `g ∘ f`. -/
theorem horizontalLiftField_smul (g : B → 𝕜) :
    hD.horizontalLiftField (g • V) = (g ∘ f) • hD.horizontalLiftField V :=
  funext fun x ↦ by
    simp only [horizontalLiftField_apply, Pi.smul_apply', comp_apply, map_smul,
      Submodule.coe_smul]

theorem horizontalLiftField_const_smul (c : 𝕜) :
    hD.horizontalLiftField (c • V) = c • hD.horizontalLiftField V :=
  funext fun x ↦ by
    simp only [horizontalLiftField_apply, Pi.smul_apply, map_smul, Submodule.coe_smul]

include hD in
/-- The derivative of `f` maps linearly independent horizontal vectors to linearly independent
vectors. -/
theorem linearIndependent_mfderiv_apply {ι : Type*} {x : P} {v : ι → TangentSpace I x}
    (hv : LinearIndependent 𝕜 v) (hvD : ∀ i, v i ∈ D x) :
    LinearIndependent 𝕜 (fun i ↦ mfderiv I J f x (v i)) :=
  hv.map (f := (mfderiv I J f x : TangentSpace I x →ₗ[𝕜] TangentSpace J (f x)))
    ((hD.isCompl_ker x).disjoint.mono_left
      (Submodule.span_le.2 (Set.range_subset_iff.2 hvD)))

section Locality

/-! ### Locality of horizontal lifts -/

variable {m : ℕ∞ω} {D' : Π x : P, Submodule 𝕜 (TangentSpace I x)}
  (hD' : IsEhresmannConnection I J m f D')

/-- Two Ehresmann connections on `f` with the same horizontal space at `x` lift vector fields
`V V'` that agree at `f x` to the same vector at `x`. -/
theorem horizontalLiftField_apply_eq_of_eq {x : P} (hx : D x = D' x)
    {V V' : Π b : B, TangentSpace J b} (hV : V (f x) = V' (f x)) :
    hD.horizontalLiftField V x = hD'.horizontalLiftField V' x := by
  rw [horizontalLiftField_apply, horizontalLiftField_apply]
  exact congrArg Subtype.val ((hD'.eq_horizontalLift_iff
    (w := ⟨_, hx ▸ (hD.horizontalLift x (V (f x))).property⟩)).2
    (by rw [mfderiv_horizontalLift, hV]))

/-- Horizontal lifts are local: if two Ehresmann connections on `f` agree near `x` and two
vector fields `V V'` agree near `f x`, then their horizontal lifts agree near `x`. -/
theorem horizontalLiftField_eventuallyEq {x : P} (hDD' : ∀ᶠ y in 𝓝 x, D y = D' y)
    {V V' : Π b : B, TangentSpace J b} (hV : V =ᶠ[𝓝 (f x)] V') :
    hD.horizontalLiftField V =ᶠ[𝓝 x] hD'.horizontalLiftField V' := by
  filter_upwards [hDD', (hD.mdifferentiable x).continuousAt.preimage_mem_nhds hV]
    with y hy hVy
  exact hD.horizontalLiftField_apply_eq_of_eq hD' hy hVy

end Locality

section Naturality

/-! ### Naturality of horizontal lifts -/

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {P' : Type*} [TopologicalSpace P'] [ChartedSpace H' P'] [IsManifold I' 1 P']
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners 𝕜 F' G'}
  {B' : Type*} [TopologicalSpace B'] [ChartedSpace G' B']
  {n' : ℕ∞ω} {f' : P' → B'} {D' : Π x : P', Submodule 𝕜 (TangentSpace I' x)}
  (hD' : IsEhresmannConnection I' J' n' f' D') {Φ : P → P'} {ψ : B → B'}

/-- **Naturality of horizontal lifts** at a point. Let `Φ : P → P'` cover `ψ : B → B'` near `x`
(`f' ∘ Φ = ψ ∘ f` near `x`), with `Φ` differentiable at `x`, `ψ` differentiable at `f x`, and
the derivative of `Φ` at `x` mapping `D x` into `D' (Φ x)`. If the derivative of `ψ` maps
`v (f x)` to `v' (f' (Φ x))`, then the derivative of `Φ` maps the horizontal lift of `v` at
`x` to the horizontal lift of `v'` at `Φ x`. -/
theorem mfderiv_horizontalLiftField_eq_of_related {x : P} {v : Π b : B, TangentSpace J b}
    {v' : Π b : B', TangentSpace J' b} (hΦ : MDifferentiableAt I I' Φ x)
    (hψ : MDifferentiableAt J J' ψ (f x)) (hfΦ : f' ∘ Φ =ᶠ[𝓝 x] ψ ∘ f)
    (hΦD : ∀ w ∈ D x, mfderiv I I' Φ x w ∈ D' (Φ x))
    (hv : mfderiv J J' ψ (f x) (v (f x)) = v' (f' (Φ x))) :
    mfderiv I I' Φ x (hD.horizontalLiftField v x) = hD'.horizontalLiftField v' (Φ x) := by
  rw [horizontalLiftField_apply, horizontalLiftField_apply]
  refine congrArg Subtype.val ((hD'.eq_horizontalLift_iff
    (w := ⟨_, hΦD _ (hD.horizontalLift x (v (f x))).property⟩)).2 ?_)
  rw [← mfderiv_comp_apply x (hD'.mdifferentiable (Φ x)) hΦ, hfΦ.mfderiv_eq,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, tangentSpaceCast_apply,
    mfderiv_comp_apply x hψ (hD.mdifferentiable x), mfderiv_horizontalLift, hv]

/-- **Naturality of horizontal lifts.** Let `Φ : P → P'` cover `ψ : B → B'` near `x`
(`f' ∘ Φ = ψ ∘ f` near `x`), with `Φ` differentiable near `x`, `ψ` differentiable near `f x`,
and the derivative of `Φ` mapping `D` into `D'` near `x`. If the vector fields `v` and `v'` are
`ψ`-related near `f x`, then their horizontal lifts are `Φ`-related near `x`. -/
theorem eventually_mfderiv_horizontalLiftField_eq_of_related {x : P}
    {v : Π b : B, TangentSpace J b} {v' : Π b : B', TangentSpace J' b}
    (hΦ : ∀ᶠ y in 𝓝 x, MDifferentiableAt I I' Φ y)
    (hψ : ∀ᶠ b in 𝓝 (f x), MDifferentiableAt J J' ψ b) (hfΦ : f' ∘ Φ =ᶠ[𝓝 x] ψ ∘ f)
    (hΦD : ∀ᶠ y in 𝓝 x, ∀ w ∈ D y, mfderiv I I' Φ y w ∈ D' (Φ y))
    (hv : ∀ᶠ b in 𝓝 (f x), mfderiv J J' ψ b (v b) = v' (ψ b)) :
    ∀ᶠ y in 𝓝 x,
      mfderiv I I' Φ y (hD.horizontalLiftField v y) = hD'.horizontalLiftField v' (Φ y) := by
  have hf := (hD.mdifferentiable x).continuousAt
  filter_upwards [hΦ, hf.preimage_mem_nhds hψ, hfΦ.eventuallyEq_nhds, hΦD,
    hf.preimage_mem_nhds hv] with y hΦy hψy hfΦy hΦDy hvy
  refine hD.mfderiv_horizontalLiftField_eq_of_related hD' hΦy hψy hfΦy hΦDy ?_
  have hy : f' (Φ y) = ψ (f y) := hfΦy.self_of_nhds
  rw [hy]
  exact hvy

end Naturality

section Smooth

/-! ### Smoothness -/

variable [IsRCLikeNormedField 𝕜] [IsManifold J 1 B]
  {EQ : Type*} [NormedAddCommGroup EQ] [NormedSpace 𝕜 EQ]
  {HQ : Type*} [TopologicalSpace HQ] {IQ : ModelWithCorners 𝕜 EQ HQ}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace HQ Q]

/-- **Horizontal lifts depend smoothly on the data.** Let `D` be a `C^n` Ehresmann connection on
`f`, with `f` of class `C^(n+1)` at `g q₀`, and let `g : Q → P` and `w : Q → TB` be `C^n` at `q₀`,
with `w q` a tangent vector at `f (g q)`. Then the horizontal lift of `w q` at `g q`, as a point
of the tangent bundle of `P`, is `C^n` in `q` at `q₀`. -/
theorem contMDiffAt_horizontalLift {g : Q → P} {w : Q → TangentBundle J B}
    (hgw : ∀ q, (w q).proj = f (g q)) {q₀ : Q} (hf : ContMDiffAt I J (n + 1) f (g q₀))
    (hg : ContMDiffAt IQ I n g q₀) (hw : ContMDiffAt IQ J.tangent n w q₀) :
    ContMDiffAt IQ I.tangent n
      (fun q ↦ (⟨g q, hD.horizontalLift (g q) (w q).snd⟩ : TangentBundle I P)) q₀ := by
  have : CompleteSpace 𝕜 := by
    let := IsRCLikeNormedField.rclike 𝕜
    infer_instance
  obtain ⟨U, hUo, hxU, X, hX⟩ := isContMDiffDistribution_iff.1 hD.isContMDiffDistribution (g q₀)
  let eB := trivializationAt F (TangentSpace J) (f (g q₀))
  -- The frame along `g`, and its image under `df`, are `C^n` along `g` and `f ∘ g`.
  have hXg (i : Fin (Module.finrank 𝕜 F)) : ContMDiffAt IQ I.tangent n
      (fun q ↦ (⟨g q, X i (g q)⟩ : TangentBundle I P)) q₀ :=
    ((hX.contMDiffOn i).contMDiffAt (hUo.mem_nhds hxU)).comp q₀ hg
  have hY (i : Fin (Module.finrank 𝕜 F)) : ContMDiffAt IQ 𝓘(𝕜, F) n
      (fun q ↦ (eB ⟨f (g q), mfderiv I J f (g q) (X i (g q))⟩).2) q₀ :=
    (contMDiffAt_totalSpace_iff.1 (hf.mfderiv_apply_sectionAlong (hXg i) le_rfl)).2
  -- The matrix of the image frame, read in the trivialization `eB`.
  let A : Q → (Fin (Module.finrank 𝕜 F) → 𝕜) →L[𝕜] F := fun q ↦
    ∑ i, (ContinuousLinearMap.proj i).smulRight
      (eB ⟨f (g q), mfderiv I J f (g q) (X i (g q))⟩).2
  have hA : ContMDiffAt IQ 𝓘(𝕜, (Fin (Module.finrank 𝕜 F) → 𝕜) →L[𝕜] F) n A q₀ :=
    contMDiffAt_finsetSum fun i _ ↦ ((ContinuousLinearMap.smulRightL 𝕜 𝕜 𝕜
      (Fin (Module.finrank 𝕜 F) → 𝕜) F
      (ContinuousLinearMap.proj i)).contDiff.contDiffAt).comp_contMDiffAt (hY i)
  have hAapply {q : Q} (hq : f (g q) ∈ eB.baseSet) (c : Fin (Module.finrank 𝕜 F) → 𝕜) :
      A q c = (eB ⟨f (g q), mfderiv I J f (g q) (∑ i, c i • X i (g q))⟩).2 := by
    have h := eB.continuousLinearMapAt_apply_of_mem (R := 𝕜) hq
    simp only [A, FunLike.coe_sum, Finset.sum_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ← h, map_sum, map_smul]
  have hb₀ : f (g q₀) ∈ eB.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
  have hAinj : Injective (A q₀) := by
    refine (injective_iff_map_eq_zero (A q₀)).2 fun c hc ↦ funext fun i ↦ ?_
    rw [hAapply hb₀, eB.snd_apply_eq_zero_iff 𝕜 hb₀, map_sum] at hc
    simp only [map_smul] at hc
    exact Fintype.linearIndependent_iff.1 (hD.linearIndependent_mfderiv_apply
      (hX.linearIndependent hxU) fun i ↦ hX.isSubbundleFrameOn.apply_mem i hxU) c hc i
  obtain ⟨L, hL, hLinv⟩ := hA.exists_contMDiffAt_leftInverse
    (.of_injective_of_finiteDimensional_domain hAinj)
  -- The coefficients of the lift in the frame, `L q` applied to `w q` read in `eB`.
  let c : Q → Fin (Module.finrank 𝕜 F) → 𝕜 := fun q ↦ L q (eB (w q)).2
  have hc : ContMDiffAt IQ 𝓘(𝕜, Fin (Module.finrank 𝕜 F) → 𝕜) n c q₀ := by
    have h := (contMDiffAt_totalSpace_iff.1 hw).2
    rw [hgw q₀] at h
    exact hL.clm_apply h
  have hsum : ContMDiffAt IQ I.tangent n
      (fun q ↦ (⟨g q, ∑ i, c q i • X i (g q)⟩ : TangentBundle I P)) q₀ :=
    ContMDiffAt.sum_sectionAlong _ _ hg fun i _ ↦
      ((ContinuousLinearMap.proj i).contDiff.contDiffAt.comp_contMDiffAt hc).smul_totalSpace (hXg i)
  refine hsum.congr_of_eventuallyEq ?_
  have hfg : ContinuousAt (f ∘ g) q₀ :=
    (hf.continuousAt).comp (f := g) hg.continuousAt
  filter_upwards [hLinv, hg.continuousAt.preimage_mem_nhds (hUo.mem_nhds hxU),
    hfg.eventually_mem_baseSet_trivializationAt F (TangentSpace J)] with q hLq hqU hqe
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).1 (by
    rw [hX.span_eq hqU]
    exact (hD.horizontalLift (g q) (w q).snd).property)
  have hw' : w q = ⟨f (g q), (w q).snd⟩ := TotalSpace.ext (hgw q) HEq.rfl
  have hca : c q = a := by
    have h : A q a = (eB (w q)).2 := by
      rw [hAapply hqe a, ha]
      exact (congrArg (fun v ↦ (eB ⟨f (g q), v⟩).2)
        (hD.mfderiv_horizontalLift (g q) (w q).snd)).trans (congrArg (fun p ↦ (eB p).2) hw'.symm)
    simp only [c, ← h]
    exact hLq a
  simp only [hca, ha]

/-- **Horizontal lifts depend smoothly on the data.** Let `D` be a `C^n` Ehresmann connection on
a `C^(n+1)` map `f`, and let `g : Q → P` and `w : Q → TB` be `C^n`, with `w q` a tangent vector at
`f (g q)`. Then the horizontal lift of `w q` at `g q`, as a point of the tangent bundle of `P`, is
`C^n` in `q`. -/
theorem contMDiff_horizontalLift {g : Q → P} {w : Q → TangentBundle J B}
    (hgw : ∀ q, (w q).proj = f (g q)) (hf : ContMDiff I J (n + 1) f)
    (hg : ContMDiff IQ I n g) (hw : ContMDiff IQ J.tangent n w) :
    ContMDiff IQ I.tangent n
      (fun q ↦ (⟨g q, hD.horizontalLift (g q) (w q).snd⟩ : TangentBundle I P)) :=
  fun q ↦ hD.contMDiffAt_horizontalLift hgw (hf (g q)) (hg q) (hw q)

/-- For a `C^n` Ehresmann connection on `f`, lifting a field `V` on `B` horizontally gives a field
that is `C^n` at `x`, provided `f` is `C^(n+1)` at `x` and `V` is `C^n` at `f x`. -/
theorem contMDiffAt_horizontalLiftField {V : Π b : B, TangentSpace J b} {x : P}
    (hf : ContMDiffAt I J (n + 1) f x) (hV : ContMDiffAt J J.tangent n (T% V) (f x)) :
    ContMDiffAt I I.tangent n (T% (hD.horizontalLiftField V)) x :=
  hD.contMDiffAt_horizontalLift (g := id) (w := fun y ↦ ⟨f y, V (f y)⟩) (fun _ ↦ rfl) hf
    contMDiffAt_id (hV.comp x (hf.of_le le_self_add))

/-- For a `C^n` Ehresmann connection on `f`, with `1 ≤ n` and `f` of class `C^2` at `x`, the
horizontal lift of a field that is `C^1` at `f x` is `C^1` at `x`. -/
theorem contMDiffAt_one_horizontalLiftField (hn : 1 ≤ n) {V : Π b : B, TangentSpace J b}
    {x : P} (hf : ContMDiffAt I J 2 f x) (hV : ContMDiffAt J J.tangent 1 (T% V) (f x)) :
    ContMDiffAt I I.tangent 1 (T% (hD.horizontalLiftField V)) x := by
  -- The lift is that of `D` seen as a `C^1` connection.
  rw [← hD.horizontalLiftField_of_le V hn]
  exact (hD.of_le hn).contMDiffAt_horizontalLiftField (by rwa [one_add_one_eq_two]) hV

/-- For a `C^n` Ehresmann connection on `f`, with `1 ≤ n` and `f` of class `C^2` at `x`, the
horizontal lift of a field that is `C^1` at `f x` is differentiable at `x`. -/
theorem mdifferentiableAt_horizontalLiftField (hn : 1 ≤ n) {V : Π b : B, TangentSpace J b}
    {x : P} (hf : ContMDiffAt I J 2 f x) (hV : ContMDiffAt J J.tangent 1 (T% V) (f x)) :
    MDifferentiableAt I I.tangent (T% (hD.horizontalLiftField V)) x :=
  (hD.contMDiffAt_one_horizontalLiftField hn hf hV).mdifferentiableAt one_ne_zero

/-- The horizontal lift of a `C^n` vector field on `B`, for a `C^n` Ehresmann connection on a
`C^(n+1)` map `f`, is `C^n`. -/
theorem contMDiff_horizontalLiftField {V : Π b : B, TangentSpace J b}
    (hf : ContMDiff I J (n + 1) f) (hV : ContMDiff J J.tangent n (T% V)) :
    ContMDiff I I.tangent n (T% (hD.horizontalLiftField V)) :=
  fun x ↦ hD.contMDiffAt_horizontalLiftField (hf x) (hV (f x))

/-- **Lifts of a frame of the base form a frame of the connection.** For a `C^n` Ehresmann
connection on a `C^(n+1)` map `f`, the horizontal lifts of a `C^n` local frame `v` of the tangent
bundle of `B` on an open set `U` form a `C^n` local frame of `D` on `f ⁻¹' U`. -/
theorem isDistributionFrameOn_horizontalLiftField {ι : Type*} [Finite ι]
    {v : ι → Π b : B, TangentSpace J b} {U : Set B} (hU : IsOpen U)
    (hv : IsDistributionFrameOn J n (fun _ ↦ ⊤) v U) (hf : ContMDiff I J (n + 1) f) :
    IsDistributionFrameOn I n D (fun i ↦ hD.horizontalLiftField (v i)) (f ⁻¹' U) where
  contMDiffOn i y hy := (hD.contMDiffAt_horizontalLiftField (hf y)
    ((hv.contMDiffOn i).contMDiffAt (hU.mem_nhds hy))).contMDiffWithinAt
  linearIndependent {y} hy := LinearIndependent.of_comp
    (mfderiv I J f y : TangentSpace I y →ₗ[𝕜] TangentSpace J (f y)) <| by
    simpa only [comp_def, ContinuousLinearMap.coe_coe, mfderiv_horizontalLiftField] using
      hv.linearIndependent hy
  span_eq {y} hy := by
    refine le_antisymm (Submodule.span_le.2 <| Set.range_subset_iff.2 fun i ↦
      hD.horizontalLiftField_mem (v i) y) fun w hw ↦ ?_
    have := Fintype.ofFinite ι
    -- The projection of `w` is a combination of the frame of the base; `w` is the same
    -- combination of the lifts.
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).1
      ((hv.span_eq hy).ge (Submodule.mem_top (x := mfderiv I J f y w)))
    have hw' : w = ∑ i, a i • hD.horizontalLiftField (v i) y := by
      have h := congrArg Subtype.val (hD.horizontalLift_mfderiv y ⟨w, hw⟩)
      simp only at h
      rw [← h, ← ha, map_sum]
      simp
    rw [hw']
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The horizontal lift of a family `V q` of vector fields on `B`, indexed by the points `q` of a
manifold `Q`, such as times in `𝕜`, and jointly `C^n` in `q` and the point, for a `C^n` Ehresmann
connection on a `C^(n+1)` map `f`, is jointly `C^n` in `q` and the point. -/
theorem contMDiff_horizontalLiftField_family {V : Q → Π b : B, TangentSpace J b}
    (hf : ContMDiff I J (n + 1) f)
    (hV : ContMDiff (IQ.prod J) J.tangent n
      (fun p : Q × B ↦ (⟨p.2, V p.1 p.2⟩ : TangentBundle J B))) :
    ContMDiff (IQ.prod I) I.tangent n
      (fun p : Q × P ↦ (⟨p.2, hD.horizontalLiftField (V p.1) p.2⟩ : TangentBundle I P)) :=
  hD.contMDiff_horizontalLift (g := Prod.snd)
    (w := fun p : Q × P ↦ ⟨f p.2, V p.1 (f p.2)⟩) (fun _ ↦ rfl) hf contMDiff_snd
    (hV.comp (contMDiff_id.prodMap (hf.of_le le_self_add)))

end Smooth

end IsEhresmannConnection

end TauCeti
