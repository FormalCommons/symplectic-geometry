/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Topology
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Pullback
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Section.Topology
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Tangent.Opens

/-!
# Two-forms in the frame topology

Tau Ceti's frame topology on the sections of a vector bundle (`ContMDiffSection.frameTopology`)
is a topology on the `C^n` two-forms of a bundle `V`, since these are the sections of the bundle
of alternating maps on `V`. This file proves that nondegeneracy over a compact subset of the base
is an open condition in it, that pulling two-forms back along the slices of a smooth family
of maps, such as the time slices of a smooth isotopy, is jointly continuous in the form and the
parameter, and that pulling them back along a single smooth map, such as the inclusion of an
open subset, is continuous. Near each point of an open subset, the frame coordinates of a two-form
and of its restriction agree.

## Main results

* `Bundle.ContMDiffTwoForm.isOpen_setOfPred_forall_mem_nondegenerate`: for a covering frame system,
  a locally compact model of the base, a bundle of finite rank and a compact `K ⊆ M`, the
  two-forms that are nondegenerate on every fibre over `K` form an open set.
* `Bundle.ContMDiffTwoForm.continuous_tangentEquiv_symm_mpullback_prod`: for a smooth family
  `f : P × M → N`, a covering frame system of the two-forms on `N` and any frame system of those
  on `M`, the map `(ω, p) ↦ tangentEquiv.symm ((tangentEquiv ω).mpullback (f (p, ·)))` is
  continuous.
* `Bundle.ContMDiffTwoForm.continuous_tangentEquiv_symm_mpullback`: its case of a smooth
  isotopy `h` from `M` to `N`, where the map is
  `(ω, t) ↦ tangentEquiv.symm ((tangentEquiv ω).mpullback (h.timeSlice t))`.
* `Bundle.ContMDiffTwoForm.continuous_tangentEquiv_symm_mpullback_of_contMDiff`: for a smooth
  map `g : M → N`, a covering frame system of the two-forms on `N` and any frame system of those
  on `M`, the map `ω ↦ tangentEquiv.symm ((tangentEquiv ω).mpullback g)` is continuous.
* `Bundle.ContMDiffTwoForm.continuous_tangentEquiv_symm_mpullback_subtypeVal`: its case of the
  inclusion of an open `U ⊆ M`, that is, the restriction of two-forms on the tangent bundle from
  `M` to `U`.
* `Bundle.ContMDiffTwoForm.trivializationAtFrameTopology`: the frame topology on the two-forms on
  the tangent bundle of `M` given by the trivializations `trivializationAt` at its points.
* `Bundle.ContMDiffTwoForm.exists_frameCoordinates_eq_frameCoordinates_mpullback_subtypeVal`: near
  each point `x` of `U`, the frame coordinates of a two-form on `M` in the trivialization at `x`
  are those of its restriction to `U` in the trivialization of the two-forms on `U` at `x`.

## Implementation notes

The proof adapts Tau Ceti's
`IsCompact.isOpen_setOf_forall_mem_forall_bilinear_apply_self_pos`
(`TauCeti/Topology/VectorBundle/Bilinear.lean`), with nondegeneracy in place of positivity: the
nondegenerate alternating maps are open in the total space of the bundle of alternating maps
(`isOpen_setOfPred_nondegenerate`), evaluation is jointly continuous in the section and the point
(`ContMDiffSection.continuous_totalSpace_eval`), and the tube lemma over `K` concludes.

Pull-back along the slices of a family `f : P × M → N` is the library's
`ContMDiffSection.continuous_pullbackMap`, with fibre maps
`ξ ↦ ξ ∘ (d(f (p, ·))ₓ × d(f (p, ·))ₓ)`. These are jointly `C^∞` on the total space of the
pull-back bundle by
`Bundle.Pullback.contMDiff_totalSpace_compContinuousLinearMap_mfderiv`. For an isotopy `h`, the
family is the motion of `h` over `unitInterval`. Pull-back along a smooth map `g : M → N` is the
slice at `0` of the constant family `(p, x) ↦ g x : ℝ × M → N`, and restriction to an open
`U ⊆ M` is its case `g = Subtype.val`.

The comparison of frame coordinates on `M` and on `U` is not definitional: it rests on the
agreement of the charts that `U` inherits with those of `M` near `x`. It takes `D` to be the
image in `M` of an open neighbourhood of `x` in `U` on which the two trivializations of the
bundles of alternating maps agree, given by
`TauCeti.Manifold.eventually_trivializationAt_continuousAlternatingMap_tangentSpace_opens_eq`,
and on which both are defined.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.6
  (symplectic vector bundles).
* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Chapter 2, §1 (the weak topology
  underlying the frame topology).
-/

public section

open Bundle TopologicalSpace
open scoped Manifold

namespace SymplecticGeometry

namespace Bundle.ContMDiffTwoForm

section Nondegenerate

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] {n : ℕ∞}
  [IsManifold I n M] [ContMDiffVectorBundle n F V I]
  {ι : Type*}
  (e : ι → Trivialization (F [⋀^Fin 2]→L[ℝ] ℝ)
    (π (F [⋀^Fin 2]→L[ℝ] ℝ) (fun x ↦ V x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x)))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- For a covering frame system, a locally compact model of the base and a bundle of finite
rank, the two-forms whose bilinear form is nondegenerate on the fibre over every point of a
compact set `K` form an open set in the frame topology. -/
theorem isOpen_setOfPred_forall_mem_nondegenerate [LocallyCompactSpace EB] [FiniteDimensional ℝ F]
    (hcover : ∀ x, ∃ i, x ∈ U i) {K : Set M} (hK : IsCompact K) :
    let _ := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
    IsOpen {ω : ContMDiffTwoForm I n F V | ∀ x ∈ K, (ω.bilinFormAt x).Nondegenerate} := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
  have hS := (isOpen_setOfPred_nondegenerate (F := F) (V := V)).preimage
    (ContMDiffSection.continuous_totalSpace_eval (I := I) (n := n) e U hU hcover)
  simp_rw [isOpen_iff_mem_nhds, bilinFormAt_def]
  exact fun ω hω ↦ hK.eventually_forall_of_forall_eventually fun x hx ↦ hS.mem_nhds (hω x hx)

end Nondegenerate

section Isotopy

open scoped ContDiff

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M] [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN}
  [TopologicalSpace N] [ChartedSpace HN N] [IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) N]
  {ι κ : Type*}
  (e : ι → Trivialization (EN [⋀^Fin 2]→L[ℝ] ℝ)
    (π (EN [⋀^Fin 2]→L[ℝ] ℝ) (fun y : N ↦ TangentSpace J y [⋀^Fin 2]→L[ℝ] Trivial N ℝ y)))
  [∀ i, MemTrivializationAtlas (e i)]
  (W : ι → Opens N) (hW : ∀ i, (W i : Set N) ⊆ (e i).baseSet)
  (e' : κ → Trivialization (EB [⋀^Fin 2]→L[ℝ] ℝ)
    (π (EB [⋀^Fin 2]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x)))
  [∀ j, MemTrivializationAtlas (e' j)]
  (W' : κ → Opens M) (hW' : ∀ j, (W' j : Set M) ⊆ (e' j).baseSet)

/-- Pulling smooth two-forms on the tangent bundle back along the slices `f (p, ·)` of a smooth
family of maps `f : P × M → N` is jointly continuous in the form and the parameter: the map
`(ω, p) ↦ tangentEquiv.symm ((tangentEquiv ω).mpullback (f (p, ·)))` is continuous from the
product of the frame topology of a covering frame system of the two-forms on `N` with `P` to the
frame topology of any frame system of the two-forms on `M`, when the models of `M` and `N` are
finite-dimensional and that of `P` is locally compact. -/
theorem continuous_tangentEquiv_symm_mpullback_prod
    {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [LocallyCompactSpace EP]
    [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P]
    [ChartedSpace HP P] [IsManifold IP ((⊤ : ℕ∞) : WithTop ℕ∞) P]
    (f : C^∞⟮IP.prod I, P × M; J, N⟯) (hcover : ∀ y, ∃ i, y ∈ W i) :
    let _ := ContMDiffSection.frameTopology (I := J) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e W hW
    let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e' W' hW'
    Continuous fun q : ContMDiffTwoForm J ⊤ EN (TangentSpace J (M := N)) × P ↦
      (tangentEquiv.symm (TauCeti.SmoothForm.mpullback (fun y ↦ f (q.2, y))
        (f.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)) (tangentEquiv q.1)) :
        ContMDiffTwoForm I ⊤ EB (TangentSpace I (M := M))) := by
  let _ := ContMDiffSection.frameTopology (I := J) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e W hW
  let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e' W' hW'
  have hΦ := Pullback.contMDiff_totalSpace_compContinuousLinearMap_mfderiv (ι := Fin 2) (G := ℝ)
    (I := I) (I' := J) (IP := IP) (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) f f.contMDiff (by simp)
  refine ((ContMDiffSection.continuous_pullbackMap f
    (fun p x ξ ↦ ξ.compContinuousLinearMap (mfderiv I J (fun y ↦ f (p, y)) x))
    hΦ e W hW hcover e' W' hW').comp continuous_swap).congr fun q ↦ ?_
  ext x v
  simp [tangentEquiv_symm_apply, tangentEquiv_apply, Function.comp_def]

/-- Pulling smooth two-forms on the tangent bundle back along the time slices of a smooth isotopy
`h` from `M` to `N` is jointly continuous in the form and the time: the map
`(ω, t) ↦ tangentEquiv.symm ((tangentEquiv ω).mpullback (h.timeSlice t))` is continuous from
the product of the frame topology of a covering frame system of the two-forms on `N` with
`unitInterval` to the frame topology of any frame system of the two-forms on `M`, when the models
of `M` and `N` are finite-dimensional. -/
theorem continuous_tangentEquiv_symm_mpullback {f₀ f₁ : C^∞⟮I, M; J, N⟯}
    (h : TauCeti.SmoothIsotopy f₀ f₁) (hcover : ∀ y, ∃ i, y ∈ W i) :
    let _ := ContMDiffSection.frameTopology (I := J) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e W hW
    let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e' W' hW'
    Continuous fun q : ContMDiffTwoForm J ⊤ EN (TangentSpace J (M := N)) × unitInterval ↦
      (tangentEquiv.symm (TauCeti.SmoothForm.mpullback (h.timeSlice q.2)
        (h.timeSlice q.2).contMDiff (tangentEquiv q.1)) :
        ContMDiffTwoForm I ⊤ EB (TangentSpace I (M := M))) := by
  have hs (t : unitInterval) : (h.timeSlice t : M → N) = fun y ↦ h.toContMDiffMap (t, y) := by
    ext y; simp
  simp_rw [hs]
  exact continuous_tangentEquiv_symm_mpullback_prod e W hW e' W' hW' h.toContMDiffMap hcover

/-- Pulling smooth two-forms on the tangent bundle back along a smooth map `g : M → N` is
continuous: the map `ω ↦ tangentEquiv.symm ((tangentEquiv ω).mpullback g)` is continuous from the
frame topology of a covering frame system of the two-forms on `N` to the frame topology of any
frame system of the two-forms on `M`, when the models of `M` and `N` are finite-dimensional. -/
theorem continuous_tangentEquiv_symm_mpullback_of_contMDiff {g : M → N}
    (hg : ContMDiff I J ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hcover : ∀ y, ∃ i, y ∈ W i) :
    let _ := ContMDiffSection.frameTopology (I := J) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e W hW
    let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e' W' hW'
    Continuous fun σ : ContMDiffTwoForm J ⊤ EN (TangentSpace J (M := N)) ↦
      (tangentEquiv.symm (TauCeti.SmoothForm.mpullback g hg (tangentEquiv σ)) :
        ContMDiffTwoForm I ⊤ EB (TangentSpace I (M := M))) := by
  let _ := ContMDiffSection.frameTopology (I := J) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e W hW
  let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e' W' hW'
  -- The pull-back along `g` is the one along the slice at `0` of the constant family
  -- `(p, x) ↦ g x : ℝ × M → N`.
  let f : C^((⊤ : ℕ∞) : WithTop ℕ∞)⟮𝓘(ℝ, ℝ).prod I, ℝ × M; J, N⟯ :=
    ⟨fun q ↦ g q.2, hg.comp contMDiff_snd⟩
  have hf (p : ℝ) : (fun y ↦ f (p, y)) = g := by ext; simp [f]
  have h := (continuous_tangentEquiv_symm_mpullback_prod e W hW e' W' hW' f hcover).comp
    (continuous_id.prodMk continuous_const : Continuous fun σ ↦ (σ, (0 : ℝ)))
  simp_rw [Function.comp_def, hf] at h
  exact h

end Isotopy

section TrivializationAt

variable {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  (I : ModelWithCorners ℝ EB HB) (M : Type*) [TopologicalSpace M] [ChartedSpace HB M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- The frame topology on the smooth two-forms on the tangent bundle of `M` given by the frames
`trivializationAt` of the bundle of two-forms at the points of `M`, each over its base set. -/
@[instance_reducible]
noncomputable def trivializationAtFrameTopology :
    TopologicalSpace (ContMDiffTwoForm I ⊤ EB (TangentSpace I (M := M))) :=
  ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (fun x : M ↦ trivializationAt (EB [⋀^Fin 2]→L[ℝ] ℝ)
      (fun y : M ↦ TangentSpace I y [⋀^Fin 2]→L[ℝ] Trivial M ℝ y) x)
    (fun x ↦ ⟨_, (trivializationAt (EB [⋀^Fin 2]→L[ℝ] ℝ)
      (fun y : M ↦ TangentSpace I y [⋀^Fin 2]→L[ℝ] Trivial M ℝ y) x).open_baseSet⟩)
    fun _ ↦ subset_rfl

theorem trivializationAtFrameTopology_def :
    trivializationAtFrameTopology I M =
      ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
        (fun x : M ↦ trivializationAt (EB [⋀^Fin 2]→L[ℝ] ℝ)
          (fun y : M ↦ TangentSpace I y [⋀^Fin 2]→L[ℝ] Trivial M ℝ y) x)
        (fun x ↦ ⟨_, (trivializationAt (EB [⋀^Fin 2]→L[ℝ] ℝ)
          (fun y : M ↦ TangentSpace I y [⋀^Fin 2]→L[ℝ] Trivial M ℝ y) x).open_baseSet⟩)
        fun _ ↦ subset_rfl :=
  (rfl)

end TrivializationAt

section Restriction

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M] [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  {U : Opens M} {ι κ : Type*}
  (e : ι → Trivialization (EB [⋀^Fin 2]→L[ℝ] ℝ)
    (π (EB [⋀^Fin 2]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x)))
  [∀ i, MemTrivializationAtlas (e i)]
  (W : ι → Opens M) (hW : ∀ i, (W i : Set M) ⊆ (e i).baseSet)
  (e' : κ → Trivialization (EB [⋀^Fin 2]→L[ℝ] ℝ)
    (π (EB [⋀^Fin 2]→L[ℝ] ℝ) (fun x : U ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] Trivial U ℝ x)))
  [∀ j, MemTrivializationAtlas (e' j)]
  (W' : κ → Opens U) (hW' : ∀ j, (W' j : Set U) ⊆ (e' j).baseSet)

/-- Restriction of smooth two-forms on the tangent bundle from `M` to an open subset `U`, that is,
pull-back along the inclusion `U → M`, is continuous from the frame topology of a covering frame
system of the two-forms on `M` to the frame topology of any frame system of the two-forms on `U`,
when the model of `M` is finite-dimensional. -/
theorem continuous_tangentEquiv_symm_mpullback_subtypeVal (hcover : ∀ x, ∃ i, x ∈ W i) :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e W hW
    let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) e' W' hW'
    Continuous fun ω : ContMDiffTwoForm I ⊤ EB (TangentSpace I (M := M)) ↦
      (tangentEquiv.symm (TauCeti.SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal
        (tangentEquiv ω)) : ContMDiffTwoForm I ⊤ EB (TangentSpace I (M := U))) := by
  exact continuous_tangentEquiv_symm_mpullback_of_contMDiff e W hW e' W' hW'
    contMDiff_subtypeVal hcover

end Restriction

section RestrictionCoordinates

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M] [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  {U : Opens M}

/-- Near each point `x` of an open `U ⊆ M`, the frame coordinates of a smooth two-form `ω` on the
tangent bundle of `M` in the trivialization at `x` are those of its restriction to `U` in the
trivialization of the two-forms on `U` at `x`: there is an open `D ⊆ U` of `M` containing `x`,
inside the base set of the first trivialization and whose preimage in `U` is inside that of the
second, such that at every `z ∈ D` the two frame coordinates over `D` and over its preimage agree,
for every `ω`. -/
theorem exists_frameCoordinates_eq_frameCoordinates_mpullback_subtypeVal (x : U) :
    ∃ (D : Opens M) (_ : (x : M) ∈ D) (hDU : (D : Set M) ⊆ U)
      (hD : (D : Set M) ⊆ (trivializationAt (EB [⋀^Fin 2]→L[ℝ] ℝ)
        (fun y : M ↦ TangentSpace I y [⋀^Fin 2]→L[ℝ] Trivial M ℝ y) (x : M)).baseSet)
      (hD' : (D.comap (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) : Set U) ⊆
        (trivializationAt (EB [⋀^Fin 2]→L[ℝ] ℝ)
          (fun y : U ↦ TangentSpace I y [⋀^Fin 2]→L[ℝ] Trivial U ℝ y) x).baseSet),
      ∀ (ω : ContMDiffTwoForm I ⊤ EB (TangentSpace I (M := M))) (z : M) (hz : z ∈ D),
        (trivializationAt _ _ (x : M)).frameCoordinates hD ω ⟨z, hz⟩ =
          (trivializationAt _ _ x).frameCoordinates hD'
            (tangentEquiv.symm (TauCeti.SmoothForm.mpullback (Subtype.val : U → M)
              contMDiff_subtypeVal (tangentEquiv ω)) :
                ContMDiffTwoForm I ⊤ EB (TangentSpace I (M := U))) ⟨⟨z, hDU hz⟩, hz⟩ := by
  obtain ⟨t, ht, hto, hxt⟩ := eventually_nhds_iff.mp
    (TauCeti.Manifold.eventually_trivializationAt_continuousAlternatingMap_tangentSpace_opens_eq
      (I := I) (G := ℝ) (ι := Fin 2) x)
  set eU := trivializationAt (EB [⋀^Fin 2]→L[ℝ] ℝ)
    (fun y : U ↦ TangentSpace I y [⋀^Fin 2]→L[ℝ] Trivial U ℝ y) x
  set eM := trivializationAt (EB [⋀^Fin 2]→L[ℝ] ℝ)
    (fun y : M ↦ TangentSpace I y [⋀^Fin 2]→L[ℝ] Trivial M ℝ y) (x : M)
  set s := t ∩ eU.baseSet ∩ Subtype.val ⁻¹' eM.baseSet
  have hs : IsOpen s :=
    (hto.inter eU.open_baseSet).inter (eM.open_baseSet.preimage continuous_subtypeVal)
  obtain ⟨D, hDs⟩ : ∃ D : Opens M, (D : Set M) = Subtype.val '' s :=
    ⟨⟨_, U.isOpen.isOpenMap_subtypeVal s hs⟩, rfl⟩
  have hDs' (y : U) : (y : M) ∈ D ↔ y ∈ s := by
    rw [← SetLike.mem_coe, hDs, Subtype.val_injective.mem_set_image]
  have hsub (y : U) (hy : (y : M) ∈ D) :
      y ∈ t ∧ y ∈ eU.baseSet ∧ (y : M) ∈ eM.baseSet := by
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := (hDs' y).1 hy
    exact ⟨h₁, h₂, h₃⟩
  have hD' : (D.comap (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) : Set U) ⊆ eU.baseSet :=
    fun y hy ↦ (hsub y (Opens.mem_comap.1 (SetLike.mem_coe.1 hy))).2.1
  have hDU : (D : Set M) ⊆ U := by
    rw [hDs]
    rintro _ ⟨y, -, rfl⟩
    exact y.property
  have hD : (D : Set M) ⊆ eM.baseSet := by
    rw [hDs]
    rintro _ ⟨y, hy, rfl⟩
    exact hy.2
  refine ⟨D, (hDs' x).2 ⟨⟨hxt, FiberBundle.mem_baseSet_trivializationAt' x⟩,
      (FiberBundle.mem_baseSet_trivializationAt' (x : M) : (x : M) ∈ eM.baseSet)⟩, hDU, hD,
    hD', fun ω z hz ↦ ?_⟩
  rw [Trivialization.frameCoordinates_apply, Trivialization.frameCoordinates_apply,
    tangentEquiv_symm_apply, TauCeti.SmoothForm.coe_mpullback_subtype_val_apply, tangentEquiv_apply]
  exact (ht ⟨z, hDU hz⟩ (hsub ⟨z, hDU hz⟩ hz).1 (ω z)).symm

end RestrictionCoordinates

end Bundle.ContMDiffTwoForm

end SymplecticGeometry

end
