/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.ManifoldLevel
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
public import TauCeti.Geometry.Manifold.MFDeriv.Opens
public import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Manifold.Submersion.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import SymplecticGeometry.Geometry.Manifold.Submersion.Basic

/-!
# Restricting a map over an open subset of its target

For a continuous map `f : M → N` and an open set `V ⊆ N`, the map `V.restrictPreimage f` sends
the open submanifold `f⁻¹(V)` of `M` to the open submanifold `V` of `N`. This file shows that
the local differential notions of `f` pass to this restriction:

* being a submersion at a point, with a given complement or not
  (`Manifold.IsSubmersionAtOfComplement.restrictPreimage`,
  `Manifold.IsSubmersionAt.restrictPreimage`), and being a submersion
  (`Manifold.IsSubmersion.restrictPreimage`). Since `Manifold.IsSubmersion` fixes one complement
  for all points, the step from a submersion at every point of `f⁻¹(V)` to a submersion on
  `f⁻¹(V)` assumes a finite-dimensional source over a complete field, where
  `Manifold.isSubmersion_iff_forall_isSubmersionAt` makes the two notions agree
  (`Manifold.IsSubmersion.restrictPreimage_of_isSubmersionAt`);
* regular points and regular values (`TauCeti.isRegularPoint_restrictPreimage_iff`,
  `TauCeti.isRegularValue_restrictPreimage_iff`);
* the regular fibre: over a regular value `b ∈ V` the fibre of the restriction and the fibre of
  `f`, each with Tau Ceti's regular-fibre atlas, are diffeomorphic by the map that keeps the
  point of `M` (`TauCeti.regularFiberRestrictPreimageDiffeomorph`).

Smoothness of the restriction is Tau Ceti's `ContMDiff.restrictPreimage`, and properness is
Mathlib's `IsProperMap.restrictPreimage`.

The proof of `Manifold.IsSubmersionAtOfComplement.restrictPreimage` adapts Tau Ceti's
`TauCeti.isImmersionAt_codRestrict_opens_iff` from immersions to submersions. It composes with
the inclusions of the open submanifolds, which are local diffeomorphisms
(`TauCeti.isLocalDiffeomorph_subtype_val`), by Tau Ceti's
`IsLocalDiffeomorphAt.isSubmersionAtOfComplement_comp` and
`IsLocalDiffeomorphAt.comp_isSubmersionAtOfComplement`, and then with a local inverse of the
inclusion of `V`. The regular-value statements use Tau Ceti's
`TauCeti.Manifold.mem_range_mfderiv_restrictPreimage_iff`. The fibre diffeomorphism follows the
pattern of Tau Ceti's `TauCeti.regularFiberRestrictDiffeomorph`, which restricts the source
instead of the target: both directions are smooth because the inclusions of the fibres are
smooth embeddings (`TauCeti.isSmoothEmbedding_coe_regularFiber`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Proposition 4.1 and Corollary 5.14.
-/

public section

open Function Module TopologicalSpace
open scoped ContDiff Manifold Topology

section Submersion

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N] {f : M → N}

namespace Manifold

/-- If `f` is a `C^n` submersion with complement `F'` at a point of `f⁻¹(V)`, for an open `V`,
then so is its restriction `f⁻¹(V) → V` at that point, with the same complement. -/
theorem IsSubmersionAtOfComplement.restrictPreimage {F' : Type*} [NormedAddCommGroup F']
    [NormedSpace 𝕜 F'] (hf : Continuous f) (V : Opens N)
    {x : (⟨f ⁻¹' V, V.isOpen.preimage hf⟩ : Opens M)}
    (h : IsSubmersionAtOfComplement F' I J n f x) :
    IsSubmersionAtOfComplement (M := (⟨f ⁻¹' V, V.isOpen.preimage hf⟩ : Opens M)) (N := V)
      F' I J n ((V : Set N).restrictPreimage f) x := by
  -- The inclusion of `V` composed with the restriction is `f` composed with the inclusion of
  -- `f⁻¹(V)`, a submersion at `x` since that inclusion is a local diffeomorphism.
  have hU : IsSubmersionAtOfComplement F' I J n
      (fun y : (⟨f ⁻¹' V, V.isOpen.preimage hf⟩ : Opens M) ↦
        ((V : Set N).restrictPreimage f y : N)) x := by
    simpa only [Set.restrictPreimage_coe, Function.comp_def] using
      IsLocalDiffeomorphAt.isSubmersionAtOfComplement_comp
        (TauCeti.isLocalDiffeomorph_subtype_val x) h
  have hV := TauCeti.isLocalDiffeomorph_subtype_val (I := J) (n := n) (U := V)
    ((V : Set N).restrictPreimage f x)
  -- Composing with a local inverse of the inclusion of `V` recovers the restriction near `x`.
  refine (IsLocalDiffeomorphAt.comp_isSubmersionAtOfComplement
    (f := fun y : (⟨f ⁻¹' V, V.isOpen.preimage hf⟩ : Opens M) ↦
      ((V : Set N).restrictPreimage f y : N))
    hV.localInverse_isLocalDiffeomorphAt hU).congr_of_eventuallyEq ?_
  exact hV.localInverse_eventuallyEq_left.comp_tendsto
    (hf.restrictPreimage (s := (V : Set N))).continuousAt

/-- If `f` is a `C^n` submersion at a point of `f⁻¹(V)`, for an open `V`, then so is its
restriction `f⁻¹(V) → V` at that point. -/
theorem IsSubmersionAt.restrictPreimage (hf : Continuous f) (V : Opens N)
    {x : (⟨f ⁻¹' V, V.isOpen.preimage hf⟩ : Opens M)} (h : IsSubmersionAt I J n f x) :
    IsSubmersionAt (M := (⟨f ⁻¹' V, V.isOpen.preimage hf⟩ : Opens M)) (N := V) I J n
      ((V : Set N).restrictPreimage f) x :=
  (h.isSubmersionAtOfComplement_complement.restrictPreimage hf V).isSubmersionAt

/-- The restriction `f⁻¹(V) → V` of a `C^n` submersion with complement `F'` over an open `V` is
a `C^n` submersion with complement `F'`. -/
theorem IsSubmersionOfComplement.restrictPreimage {F' : Type*} [NormedAddCommGroup F']
    [NormedSpace 𝕜 F'] (h : IsSubmersionOfComplement F' I J n f) (hf : Continuous f)
    (V : Opens N) :
    IsSubmersionOfComplement (M := (⟨f ⁻¹' V, V.isOpen.preimage hf⟩ : Opens M)) (N := V)
      F' I J n ((V : Set N).restrictPreimage f) :=
  isSubmersionOfComplement_iff.2 fun x ↦ (h.isSubmersionAt x).restrictPreimage hf V

/-- The restriction `f⁻¹(V) → V` of a `C^n` submersion over an open `V` is a `C^n`
submersion. -/
theorem IsSubmersion.restrictPreimage (h : IsSubmersion I J n f) (hf : Continuous f)
    (V : Opens N) :
    IsSubmersion (M := (⟨f ⁻¹' V, V.isOpen.preimage hf⟩ : Opens M)) (N := V) I J n
      ((V : Set N).restrictPreimage f) :=
  (h.isSubmersionOfComplement_complement.restrictPreimage hf V).isSubmersion

end Manifold

end Submersion

section SubmersionFiniteDimensional

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N] {f : M → N}

/-- For a continuous map `f` from a manifold modelled on a finite-dimensional space over a
complete field, and an open `V` such that `f` is a `C^n` submersion at every point of `f⁻¹(V)`,
the restriction `f⁻¹(V) → V` is a `C^n` submersion. -/
theorem Manifold.IsSubmersion.restrictPreimage_of_isSubmersionAt (hf : Continuous f)
    (V : Opens N) (h : ∀ x ∈ f ⁻¹' V, IsSubmersionAt I J n f x) :
    IsSubmersion (M := (⟨f ⁻¹' V, V.isOpen.preimage hf⟩ : Opens M)) (N := V) I J n
      ((V : Set N).restrictPreimage f) :=
  Manifold.isSubmersion_iff_forall_isSubmersionAt.2 fun x ↦ (h x x.property).restrictPreimage hf V

end SubmersionFiniteDimensional

namespace TauCeti

section Regular

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {f : M → N}

/-- A point of `f⁻¹(V)`, for an open `V`, is a regular point of the restriction `f⁻¹(V) → V`
exactly when it is a regular point of `f`. -/
theorem isRegularPoint_restrictPreimage_iff (hf : Continuous f) (V : Opens N)
    {x : (⟨f ⁻¹' V, V.isOpen.preimage hf⟩ : Opens M)} :
    IsRegularPoint (M := (⟨f ⁻¹' V, V.isOpen.preimage hf⟩ : Opens M)) (N := V) I J
      ((V : Set N).restrictPreimage f) x ↔ IsRegularPoint I J f x := by
  simp only [isRegularPoint_iff, Surjective]
  exact forall_congr' fun v ↦ LinearMap.mem_range.symm.trans
    ((Manifold.mem_range_mfderiv_restrictPreimage_iff hf V).trans LinearMap.mem_range)

/-- A value `b ∈ V`, for an open `V`, is a regular value of the restriction `f⁻¹(V) → V`
exactly when it is a regular value of `f`. -/
theorem isRegularValue_restrictPreimage_iff (hf : Continuous f) (V : Opens N) {b : N}
    (hb : b ∈ V) :
    IsRegularValue (M := (⟨f ⁻¹' V, V.isOpen.preimage hf⟩ : Opens M)) (N := V) I J
      ((V : Set N).restrictPreimage f) ⟨b, hb⟩ ↔ IsRegularValue I J f b := by
  rw [isRegularValue_iff, isRegularValue_iff]
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · have hxV : f x ∈ V := hx ▸ hb
    exact (isRegularPoint_restrictPreimage_iff (x := ⟨x, hxV⟩) hf V).1
      (h ⟨x, hxV⟩ (Subtype.ext hx))
  · exact (isRegularPoint_restrictPreimage_iff hf V).2 (h x (congrArg Subtype.val hx))

end Regular

section Fiber

variable {E H M F G N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {m : ℕ∞ω} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I m M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G}
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J m N]
  {f : M → N} {b : N}

/-- Over a regular value `b ∈ V` in the interior, for an open `V`, the fibre over `b` of the
restriction `f⁻¹(V) → V` of a `C^m` map `f` and the fibre of `f` over `b` are `C^m`
diffeomorphic, each with its regular-fibre atlas. The diffeomorphism keeps the point of `M`
(`TauCeti.coe_regularFiberRestrictPreimageDiffeomorph_apply`). -/
noncomputable def regularFiberRestrictPreimageDiffeomorph (hm : 1 ≤ m) (hf : ContMDiff I J m f)
    (hc : J.IsInteriorPoint b) (hreg : IsRegularValue I J f b) (V : Opens N) (hb : b ∈ V) :
    letI := regularFiberChartedSpace hm
      (hf.restrictPreimage V)
      (ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val.2 hc)
      ((isRegularValue_restrictPreimage_iff hf.continuous V hb).2 hreg)
    letI := regularFiberChartedSpace hm hf hc hreg
    {x : ↥(⟨f ⁻¹' V, V.isOpen.preimage hf.continuous⟩ : Opens M) //
        (V : Set N).restrictPreimage f x = ⟨b, hb⟩} ≃ₘ^m⟮
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ), 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ)⟯
      {x : M // f x = b} :=
  letI := regularFiberChartedSpace hm
    (hf.restrictPreimage V)
    (ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val.2 hc)
    ((isRegularValue_restrictPreimage_iff hf.continuous V hb).2 hreg)
  letI := regularFiberChartedSpace hm hf hc hreg
  have hV := isSmoothEmbedding_coe_regularFiber hm
    (hf.restrictPreimage V)
    (ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val.2 hc)
    ((isRegularValue_restrictPreimage_iff hf.continuous V hb).2 hreg)
  have hM := isSmoothEmbedding_coe_regularFiber hm hf hc hreg
  { toFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
    invFun x := ⟨⟨x.val, show f x.val ∈ V by rw [x.property]; exact hb⟩, Subtype.ext x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    contMDiff_toFun := hM.contMDiff_iff_comp.2 (contMDiff_subtypeVal.comp hV.contMDiff)
    contMDiff_invFun := hV.contMDiff_iff_comp.2 ((ContMDiff.subtypeVal_comp_iff _ _).1
      hM.contMDiff) }

/-- The diffeomorphism `TauCeti.regularFiberRestrictPreimageDiffeomorph` keeps the point
of `M`. -/
@[simp]
theorem coe_regularFiberRestrictPreimageDiffeomorph_apply (hm : 1 ≤ m)
    (hf : ContMDiff I J m f) (hc : J.IsInteriorPoint b) (hreg : IsRegularValue I J f b)
    (V : Opens N) (hb : b ∈ V)
    (x : {x : ↥(⟨f ⁻¹' V, V.isOpen.preimage hf.continuous⟩ : Opens M) //
        (V : Set N).restrictPreimage f x = ⟨b, hb⟩}) :
    letI := regularFiberChartedSpace hm (hf.restrictPreimage V)
      (ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val.2 hc)
      ((isRegularValue_restrictPreimage_iff hf.continuous V hb).2 hreg)
    letI := regularFiberChartedSpace hm hf hc hreg
    (regularFiberRestrictPreimageDiffeomorph hm hf hc hreg V hb x : M) = x.val.val :=
  (rfl)

/-- The inverse of `TauCeti.regularFiberRestrictPreimageDiffeomorph` keeps the point of `M`. -/
@[simp]
theorem coe_coe_regularFiberRestrictPreimageDiffeomorph_symm_apply (hm : 1 ≤ m)
    (hf : ContMDiff I J m f) (hc : J.IsInteriorPoint b) (hreg : IsRegularValue I J f b)
    (V : Opens N) (hb : b ∈ V) (x : {x : M // f x = b}) :
    letI := regularFiberChartedSpace hm (hf.restrictPreimage V)
      (ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val.2 hc)
      ((isRegularValue_restrictPreimage_iff hf.continuous V hb).2 hreg)
    letI := regularFiberChartedSpace hm hf hc hreg
    ((((regularFiberRestrictPreimageDiffeomorph hm hf hc hreg V hb).symm x).val : _) : M) =
      x.val :=
  (rfl)

end Fiber

end TauCeti

end
