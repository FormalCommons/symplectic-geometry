/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Submersion.EhresmannConnection.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Basic
import TauCeti.Analysis.Normed.Module.ContinuousInverse
import TauCeti.Geometry.Manifold.ContMDiff.LeftInverse
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity

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
(`TauCeti.IsRiemannianSubmersion.horizontalLift_eq_isEhresmannConnection_horizontalLift`), so
results about general connections apply to it.

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
* `TauCeti.IsEhresmannConnection.contMDiffAt_horizontalLift` and
  `TauCeti.IsEhresmannConnection.contMDiff_horizontalLift`: horizontal lifts of tangent vectors
  depend smoothly on their base point and on the vector.
* `TauCeti.IsEhresmannConnection.contMDiff_horizontalLiftField` and
  `TauCeti.IsEhresmannConnection.contMDiff_horizontalLiftField_timeDependent`: the horizontal
  lift of a smooth vector field, or of a time-dependent one, jointly in time and point, is smooth.
* `TauCeti.IsEhresmannConnection.mdifferentiableAt_horizontalLiftField`: for a `C^n` connection
  with `1 ≤ n`, the horizontal lift of a `C^n` field is differentiable.
* `TauCeti.IsRiemannianSubmersion.horizontalLift_eq_isEhresmannConnection_horizontalLift`: the
  horizontal lift of a Riemannian submersion is that of its orthogonal Ehresmann connection.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.3.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §9.
-/

public section

noncomputable section

open Function Bundle
open scoped ContDiff Manifold

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
    rw [hAapply hb₀, ← Trivialization.linearEquivAt_apply (R := 𝕜) _ _ hb₀,
      LinearEquiv.map_eq_zero_iff, map_sum] at hc
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
    hfg.preimage_mem_nhds (eB.open_baseSet.mem_nhds hb₀)] with q hLq hqU hqe
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

/-- For a `C^n` Ehresmann connection on `f`, with `1 ≤ n` and `f` of class `C^(n+1)` at `x`, the
horizontal lift of a field that is `C^n` at `f x` is differentiable at `x`. -/
theorem mdifferentiableAt_horizontalLiftField (hn : 1 ≤ n) {V : Π b : B, TangentSpace J b}
    {x : P} (hf : ContMDiffAt I J (n + 1) f x) (hV : ContMDiffAt J J.tangent n (T% V) (f x)) :
    MDifferentiableAt I I.tangent (T% (hD.horizontalLiftField V)) x :=
  ((hD.contMDiffAt_horizontalLiftField hf hV).of_le hn).mdifferentiableAt one_ne_zero

/-- The horizontal lift of a `C^n` vector field on `B`, for a `C^n` Ehresmann connection on a
`C^(n+1)` map `f`, is `C^n`. -/
theorem contMDiff_horizontalLiftField {V : Π b : B, TangentSpace J b}
    (hf : ContMDiff I J (n + 1) f) (hV : ContMDiff J J.tangent n (T% V)) :
    ContMDiff I I.tangent n (T% (hD.horizontalLiftField V)) :=
  fun x ↦ hD.contMDiffAt_horizontalLiftField (hf x) (hV (f x))

/-- The horizontal lift of a time-dependent vector field `V` on `B`, jointly `C^n` in time and
point, for a `C^n` Ehresmann connection on a `C^(n+1)` map `f`, is jointly `C^n` in time and
point. -/
theorem contMDiff_horizontalLiftField_timeDependent {V : 𝕜 → Π b : B, TangentSpace J b}
    (hf : ContMDiff I J (n + 1) f)
    (hV : ContMDiff (𝓘(𝕜, 𝕜).prod J) J.tangent n
      (fun p : 𝕜 × B ↦ (⟨p.2, V p.1 p.2⟩ : TangentBundle J B))) :
    ContMDiff (𝓘(𝕜, 𝕜).prod I) I.tangent n
      (fun p : 𝕜 × P ↦ (⟨p.2, hD.horizontalLiftField (V p.1) p.2⟩ : TangentBundle I P)) :=
  hD.contMDiff_horizontalLift (g := Prod.snd)
    (w := fun p : 𝕜 × P ↦ ⟨f p.2, V p.1 (f p.2)⟩) (fun _ ↦ rfl) hf contMDiff_snd
    (hV.comp (contMDiff_id.prodMap (hf.of_le le_self_add)))

end Smooth

end IsEhresmannConnection

namespace IsRiemannianSubmersion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I 1 P]
  [RiemannianBundle (fun x : P ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {B : Type*} [TopologicalSpace B] [ChartedSpace G B]
  [RiemannianBundle (fun b : B ↦ TangentSpace J b)]
  {n : ℕ∞ω} {f : P → B}

/-- The horizontal lift of a Riemannian submersion, by the metric adjoint of its derivative, is
the horizontal lift of the Ehresmann connection formed by the orthogonal complements of its
vertical spaces, such as the one given by
`Manifold.IsSubmersion.isEhresmannConnection_orthogonal_ker_mfderiv`. -/
theorem horizontalLift_eq_isEhresmannConnection_horizontalLift
    (h : IsRiemannianSubmersion I J f)
    (hD : IsEhresmannConnection I J n f (fun x ↦ (mfderiv I J f x).kerᗮ))
    (x : P) (v : TangentSpace J (f x)) :
    h.horizontalLift x v = hD.horizontalLift x v :=
  congrArg Subtype.val ((hD.eq_horizontalLift_iff
    (w := ⟨h.horizontalLift x v, h.horizontalLift_mem_orthogonal_ker x v⟩)).2
    (h.mfderiv_horizontalLift x v))

end IsRiemannianSubmersion

end TauCeti
