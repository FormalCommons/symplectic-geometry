/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DeRham.HomotopyInvariance
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic
import SymplecticGeometry.Geometry.Manifold.DeRham.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# Pullbacks of closed forms

A complement to Tau Ceti's `TauCeti/Geometry/Manifold/DeRham/Map.lean`: the membership form of
the fact that a smooth map pulls closed forms back to closed forms,
`TauCeti.SmoothForm.mpullback_mem_closedForms`. It lets a caller state closedness of
`SmoothForm.mpullback f hf φ` directly, without passing through the subtype map
`TauCeti.closedForms.mpullback`. Also the form-level consequence of homotopy invariance,
`TauCeti.SmoothForm.mpullback_sub_mem_exactForms_of_homotopy`: smoothly homotopic maps pull a
closed form back to forms that differ by an exact form, and its case for the slices of a smooth
map `F : [0, 1] × M → M'`,
`TauCeti.SmoothForm.mpullback_slice_zero_sub_mpullback_slice_mem_exactForms`, through the
homotopy `(x, s) ↦ F (s t, x)`; in particular for the slices of a smooth isotopy,
`TauCeti.SmoothForm.mpullback_sub_mpullback_timeSlice_mem_exactForms`. Finally, the class-level
form of an identity of pull-backs, `TauCeti.deRhamCohomology.map_mk_eq_mk_of_mpullback_eq`: a
smooth map that pulls a closed form `α` back to a closed form `β` sends the class of `α` to that
of `β`; in particular, a diffeomorphism in the stabilizer of a closed form fixes its class,
`TauCeti.deRhamCohomology.map_mk_of_mem_diffeomorphStabilizer`.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §2 (pullback
  commutes with the exterior derivative) and §4 (homotopy invariance).
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H E' H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {M M' : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 2 M']

/-- The pullback of a closed smooth form along a smooth map is closed. -/
theorem mpullback_mem_closedForms (f : M → M') (hf : ContMDiff I I' ∞ f) {k : ℕ}
    {φ : SmoothForm I' M' ℝ k} (hφ : φ ∈ closedForms I' M' k) :
    SmoothForm.mpullback f hf φ ∈ closedForms I M k := by
  rw [mem_closedForms_iff_mextDerivₗ_eq_zero, SmoothForm.mextDerivₗ_mpullback,
    (mem_closedForms_iff_mextDerivₗ_eq_zero I' φ).mp hφ, map_zero]

/-- **Homotopic maps pull back closed forms to cohomologous forms.** If `F : M × [0, 1] → M'`
is a smooth homotopy from `f` to `g`, then for every closed real form `γ` on `M'` the difference
`f^* γ - g^* γ` is exact. -/
theorem mpullback_sub_mem_exactForms_of_homotopy [IsManifold I ∞ M] {f g : M → M'}
    (hf : ContMDiff I I' ∞ f) (hg : ContMDiff I I' ∞ g) {F : M × Set.Icc (0 : ℝ) 1 → M'}
    (hF : ContMDiff (I.prod (𝓡∂ 1)) I' ∞ F) (h₀ : ∀ x, F (x, 0) = f x)
    (h₁ : ∀ x, F (x, 1) = g x) {k : ℕ} {γ : SmoothForm I' M' ℝ k}
    (hγ : γ ∈ closedForms I' M' k) :
    SmoothForm.mpullback f hf γ - SmoothForm.mpullback g hg γ ∈ exactForms I M k := by
  have h := congrArg (· (deRhamCohomology.mk I' k ⟨γ, hγ⟩))
    (deRhamCohomology.map_eq_of_homotopy hf hg hF h₀ h₁ k)
  simp only [deRhamCohomology.map_mk] at h
  rw [deRhamCohomology.mk_eq_mk_iff] at h
  simpa using h

/-- The slices of a smooth map `F : [0, 1] × M → M'` pull a closed form `γ` back into one
class: for every time `t`, the difference `F(0, ·)^* γ - F(t, ·)^* γ` is exact. -/
theorem mpullback_slice_zero_sub_mpullback_slice_mem_exactForms [IsManifold I ∞ M]
    {F : unitInterval × M → M'} (hF : ContMDiff ((𝓡∂ 1).prod I) I' ∞ F) (t : unitInterval)
    {k : ℕ} {γ : SmoothForm I' M' ℝ k} (hγ : γ ∈ closedForms I' M' k) :
    SmoothForm.mpullback (fun x ↦ F (0, x)) (hF.comp (contMDiff_const.prodMk contMDiff_id)) γ -
        SmoothForm.mpullback (fun x ↦ F (t, x)) (hF.comp (contMDiff_const.prodMk contMDiff_id))
          γ ∈
      exactForms I M k :=
  mpullback_sub_mem_exactForms_of_homotopy _ _
    (F := fun q : M × Set.Icc (0 : ℝ) 1 ↦ F (Set.Icc.convexComb 0 t q.2, q.1))
    (hF.comp ((contMDiff_const.convexComb contMDiff_const contMDiff_snd).prodMk
      contMDiff_fst)) (fun x ↦ by simp) (fun x ↦ by simp) hγ

/-- The slices of a smooth isotopy `h` from `f₀` pull a closed form `γ` back into one class:
for every time `t`, the difference `f₀^* γ - (h_t)^* γ` is exact, where `h_t` is the slice of
`h` at time `t`. -/
theorem mpullback_sub_mpullback_timeSlice_mem_exactForms [IsManifold I ∞ M]
    {f₀ f₁ : C^∞⟮I, M; I', M'⟯} (h : SmoothIsotopy f₀ f₁) (t : unitInterval) {k : ℕ}
    {γ : SmoothForm I' M' ℝ k} (hγ : γ ∈ closedForms I' M' k) :
    SmoothForm.mpullback f₀ f₀.contMDiff γ -
        SmoothForm.mpullback (h.timeSlice t) (h.timeSlice t).contMDiff γ ∈
      exactForms I M k := by
  rw [SmoothForm.mpullback_congr _ (h.contMDiff.comp (contMDiff_const.prodMk contMDiff_id))
      (funext fun x ↦ (h.apply_zero x).symm),
    SmoothForm.mpullback_congr _ (h.contMDiff.comp (contMDiff_const.prodMk contMDiff_id))
      (funext (h.timeSlice_apply t))]
  exact mpullback_slice_zero_sub_mpullback_slice_mem_exactForms h.contMDiff t hγ

end TauCeti.SmoothForm

namespace TauCeti.deRhamCohomology

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]

/-- **Classes of pull-backs.** If a smooth map `f : M → M'` pulls a closed form `α` on `M'`
back to a closed form `β` on `M`, the map that `f` induces on de Rham cohomology sends the class
of `α` to that of `β`. -/
theorem map_mk_eq_mk_of_mpullback_eq {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {M' : Type*} [TopologicalSpace M']
    [ChartedSpace H' M'] [IsManifold I' 2 M'] {f : M → M'} (hf : ContMDiff I I' ∞ f) {k : ℕ}
    {α : closedForms I' M' k} {β : closedForms I M k}
    (h : SmoothForm.mpullback f hf α.val = β.val) :
    map f hf k (mk I' k α) = mk I k β := by
  rw [map_mk]
  congr 1
  ext1
  rw [closedForms.coe_mpullback]
  exact h

/-- **A diffeomorphism that preserves a closed form fixes its class.** If `φ` lies in the
stabilizer of a closed form `σ`, the map that `φ` induces on de Rham cohomology sends the class
of `σ` to itself. -/
theorem map_mk_of_mem_diffeomorphStabilizer {k : ℕ} {σ : closedForms I M k}
    {φ : M ≃ₘ⟮I, I⟯ M} (hφ : φ ∈ SmoothForm.diffeomorphStabilizer σ.val) :
    map φ φ.contMDiff k (mk I k σ) = mk I k σ :=
  map_mk_eq_mk_of_mpullback_eq _ (SmoothForm.mem_diffeomorphStabilizer.1 hφ)

end TauCeti.deRhamCohomology

end
