/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.ProjectiveSpace
public import SymplecticGeometry.Geometry.Manifold.Projectivization.TwistCore

/-!
# `𝒪(-1)` is the tautological line

On the projective space `ℙ 𝕜 (Fin (n + 1) → 𝕜)`, Tau Ceti's line bundle
`Projectivization.twistCore (-1)`, glued from trivial lines along the transition functions
`twistTransition (-1)`, is isomorphic to the tautological line `Projectivization.Tautological`,
whose fibre over a point is the line itself. In the frame of the standard chart `i`, a vector `w`
of the line `x` is its coordinate `w i`, and these coordinates change from chart to chart by
`twistTransition (-1)` (Tau Ceti's `Projectivization.twistTransition_neg_one_mul`).

## Main definitions and results

* `Projectivization.tautologicalTwistCoreEquiv x`: the isomorphism of the line `x` with the fibre
  of `𝒪(-1)` at `x`, which sends `w` to its coordinate `w c` for the preferred chart `c` of
  `𝒪(-1)` at `x`.
* `Projectivization.twistCore_localTriv_tautologicalTwistCoreEquiv`: in the chart `i` of `𝒪(-1)`,
  at every point, it sends `w` to `w i`; `simp` proves it through its form in the coordinate
  changes, `twistCore_coordChange_indexAt_tautologicalTwistCoreEquiv`.
* `Projectivization.continuous_tautologicalTwistCoreEquiv` and
  `Projectivization.continuous_tautologicalTwistCoreEquiv_symm`: it is continuous on total spaces
  in both directions; `Projectivization.contMDiff_coe_tautologicalTwistCoreEquiv_symm`: the
  inverse, read as a vector of `𝕜^{n+1}`, is `C^r` on the total space of `𝒪(-1)`.
* `Projectivization.complexEulerClass_twistCore_neg_one`: over `ℂ`, the Euler class of `𝒪(-1)`,
  read in integral cohomology, is minus the hyperplane class.
* `Projectivization.complexEulerClass_twistCore_zero`: over `ℂ`, the Euler class of the trivial
  bundle `𝒪(0)` is zero, through the global section `1` of
  `Projectivization.twistCoreZeroTrivialization`.

## Implementation notes

The continuity on total spaces is checked in the trivializations of `twistCore (-1)` and in the
subspace topology of the tautological line, as for `Projectivization.twistCoreTensorEquiv`. Both
directions are proved directly, so that the scalars are any nontrivially normed field, with no
completeness and no `SeparatingDual` instance.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 1,
  §1 (the universal line bundle on projective space and its transition functions).
* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §20 (the
  tautological line of a projective space and the class `x = -e(S)`).
-/

public section

noncomputable section

open Bundle Module Set Topology TauCeti
open scoped LinearAlgebra.Projectivization ContDiff Manifold

namespace Projectivization

section Equiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ}

/-- The fibrewise isomorphism of the tautological line of `ℙ 𝕜 (Fin (n + 1) → 𝕜)` with `𝒪(-1)`:
a vector `w` of the line `x` goes to its coordinate `w c`, where `c` is the preferred chart of
`twistCore (-1)` at `x`; the inverse sends `a` to `a` times the representative of `x` whose
coordinate `c` is `1`. In the chart `i` it is `w ↦ w i`
(`twistCore_localTriv_tautologicalTwistCoreEquiv`). -/
def tautologicalTwistCoreEquiv (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    Tautological 𝕜 (Fin (n + 1) → 𝕜) x ≃L[𝕜] (twistCore (-1)).Fiber x where
  toFun w := (w : Fin (n + 1) → 𝕜) ((twistCore (-1)).indexAt x)
  -- The fibres of `twistCore` are `𝕜`.
  invFun (a : 𝕜) := ⟨a • normalizedRep (LinearMap.proj ((twistCore (𝕜 := 𝕜) (-1)).indexAt x)) x,
    Submodule.smul_mem _ _ (normalizedRep_mem_submodule _ _)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv w := Subtype.ext <| apply_smul_normalizedRep
    ((affineOpen_eq_linearProjectionDomain _).subset (mem_affineOpen_twistCore_indexAt (-1) x))
    w.property
  right_inv (a : 𝕜) := by
    have h := apply_normalizedRep
      ((affineOpen_eq_linearProjectionDomain (K := 𝕜) _).subset
        (mem_affineOpen_twistCore_indexAt (n := n) (-1) x))
    rw [LinearMap.proj_apply] at h
    -- The goal is the coordinate `c` of `a • normalizedRep _ x`, that is `a * _ = a`.
    exact (congrArg (a * ·) h).trans (mul_one a)
  continuous_toFun := (continuous_apply _).comp continuous_subtypeVal
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop

theorem tautologicalTwistCoreEquiv_apply (x : ℙ 𝕜 (Fin (n + 1) → 𝕜))
    (w : Tautological 𝕜 (Fin (n + 1) → 𝕜) x) :
    tautologicalTwistCoreEquiv x w = (w : Fin (n + 1) → 𝕜) ((twistCore (-1)).indexAt x) := by
  rfl

theorem coe_tautologicalTwistCoreEquiv_symm_apply (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) (a : 𝕜) :
    ((tautologicalTwistCoreEquiv x).symm a : Fin (n + 1) → 𝕜) =
      a • normalizedRep (LinearMap.proj ((twistCore (𝕜 := 𝕜) (-1)).indexAt x)) x := by
  rfl

/-- The coordinate change of `𝒪(-1)` from its preferred chart at `x` to the chart `i` sends
the image of a vector `w` of the line under `tautologicalTwistCoreEquiv` to its coordinate
`w i`. This is the simp normal form of `twistCore_localTriv_tautologicalTwistCoreEquiv`. -/
@[simp]
theorem twistCore_coordChange_indexAt_tautologicalTwistCoreEquiv (i : Fin (n + 1))
    {x : ℙ 𝕜 (Fin (n + 1) → 𝕜)} (w : Tautological 𝕜 (Fin (n + 1) → 𝕜) x) :
    (twistCore (-1)).coordChange ((twistCore (-1)).indexAt x) i x
        (tautologicalTwistCoreEquiv x w) = (w : Fin (n + 1) → 𝕜) i := by
  simp only [twistCore_coordChange_apply, tautologicalTwistCoreEquiv_apply]
  exact twistTransition_neg_one_mul i (mem_affineOpen_twistCore_indexAt (-1) x) w.property

/-- **`tautologicalTwistCoreEquiv` in the standard charts.** Read through the chart `i` of
`𝒪(-1)`, `tautologicalTwistCoreEquiv` sends a vector `w` of the line to its coordinate `w i`. -/
theorem twistCore_localTriv_tautologicalTwistCoreEquiv (i : Fin (n + 1))
    {x : ℙ 𝕜 (Fin (n + 1) → 𝕜)} (w : Tautological 𝕜 (Fin (n + 1) → 𝕜) x) :
    ((twistCore (-1)).localTriv i ⟨x, tautologicalTwistCoreEquiv x w⟩).2 =
      (w : Fin (n + 1) → 𝕜) i := by
  simp

/-- Over the standard affine open `U_i`, the inverse of `tautologicalTwistCoreEquiv` sends a
vector of `𝒪(-1)` to its coordinate in the chart `i` times the representative of the line whose
coordinate `i` is `1`. -/
theorem coe_tautologicalTwistCoreEquiv_symm_apply_of_mem {i : Fin (n + 1)}
    {x : ℙ 𝕜 (Fin (n + 1) → 𝕜)} (hx : x ∈ affineOpen i)
    (a : (twistCore (𝕜 := 𝕜) (n := n) (-1)).Fiber x) :
    ((tautologicalTwistCoreEquiv x).symm a : Fin (n + 1) → 𝕜) =
      ((twistCore (-1)).localTriv i ⟨x, a⟩).2 • normalizedRep (LinearMap.proj i) x := by
  conv_rhs => rw [← (tautologicalTwistCoreEquiv x).apply_symm_apply a,
    twistCore_localTriv_tautologicalTwistCoreEquiv i]
  exact (apply_smul_normalizedRep ((affineOpen_eq_linearProjectionDomain i).subset hx)
    ((tautologicalTwistCoreEquiv x).symm a).property).symm

/-- `tautologicalTwistCoreEquiv` is continuous on total spaces. -/
theorem continuous_tautologicalTwistCoreEquiv :
    Continuous fun v : TotalSpace 𝕜 (Tautological 𝕜 (Fin (n + 1) → 𝕜)) ↦
      TotalSpace.mk' 𝕜 (E := (twistCore (-1)).Fiber) v.proj
        (tautologicalTwistCoreEquiv v.proj v.snd) := by
  refine continuous_iff_continuousAt.2 fun v₀ ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(continuous_proj_tautological 𝕜 _).continuousAt, ?_⟩
  exact ((continuous_apply ((twistCore (𝕜 := 𝕜) (n := n) (-1)).indexAt v₀.proj)).comp
    (continuous_snd_tautological 𝕜 _)).continuousAt.congr (.of_forall fun v ↦
      (twistCore_localTriv_tautologicalTwistCoreEquiv _ v.snd).symm)

/-- The inverse of `tautologicalTwistCoreEquiv` is continuous on total spaces. -/
theorem continuous_tautologicalTwistCoreEquiv_symm :
    Continuous fun q : TotalSpace 𝕜 (twistCore (𝕜 := 𝕜) (n := n) (-1)).Fiber ↦
      TotalSpace.mk' 𝕜 (E := Tautological 𝕜 (Fin (n + 1) → 𝕜)) q.proj
        ((tautologicalTwistCoreEquiv q.proj).symm q.snd) := by
  refine continuous_totalSpace_tautological_iff.2
    ⟨FiberBundle.continuous_proj _ _, continuous_iff_continuousAt.2 fun q₀ ↦ ?_⟩
  set i := (twistCore (𝕜 := 𝕜) (n := n) (-1)).indexAt q₀.proj
  have hi₀ : q₀.proj ∈ affineOpen i := mem_affineOpen_twistCore_indexAt (-1) q₀.proj
  have hU : ∀ᶠ q in 𝓝 q₀, q.proj ∈ affineOpen i :=
    (FiberBundle.continuous_proj _ _).continuousAt.preimage_mem_nhds
      ((isOpen_affineOpen i).mem_nhds hi₀)
  refine ContinuousAt.congr ?_
    (hU.mono fun q hq ↦ (coe_tautologicalTwistCoreEquiv_symm_apply_of_mem hq q.snd).symm)
  have h₁ : ContinuousAt (fun q ↦ ((twistCore (𝕜 := 𝕜) (n := n) (-1)).localTriv i q).2) q₀ :=
    continuous_snd.continuousAt.comp (((twistCore (-1)).localTriv i).continuousAt
      (((twistCore (-1)).mem_localTriv_source (i := i) q₀).2
        (by simpa [twistCore_baseSet] using hi₀)))
  have h₂ : ContinuousAt (fun q : TotalSpace 𝕜 (twistCore (𝕜 := 𝕜) (n := n) (-1)).Fiber ↦
      normalizedRep (LinearMap.proj (R := 𝕜) (φ := fun _ : Fin (n + 1) ↦ 𝕜) i) q.proj) q₀ :=
    ((continuousOn_normalizedRep (continuous_apply i)).continuousAt
      (Filter.mem_of_superset ((isOpen_affineOpen i).mem_nhds hi₀)
        (affineOpen_eq_linearProjectionDomain i).subset)).comp
      (FiberBundle.continuous_proj _ _).continuousAt
  exact h₁.smul h₂

/-- The inverse of `tautologicalTwistCoreEquiv`, read as a vector of `𝕜^{n+1}`, is `C^r` on the
total space of `𝒪(-1)`, for every `r` including the analytic order `ω`. -/
theorem contMDiff_coe_tautologicalTwistCoreEquiv_symm (r : ℕ∞ω) :
    ContMDiff (𝓘(𝕜, Fin n → 𝕜).prod 𝓘(𝕜, 𝕜)) 𝓘(𝕜, Fin (n + 1) → 𝕜) r
      fun q : TotalSpace 𝕜 (twistCore (𝕜 := 𝕜) (n := n) (-1)).Fiber ↦
        ((tautologicalTwistCoreEquiv q.proj).symm q.snd : Fin (n + 1) → 𝕜) := by
  intro q₀
  set i := (twistCore (𝕜 := 𝕜) (n := n) (-1)).indexAt q₀.proj
  have hi₀ : q₀.proj ∈ affineOpen i := mem_affineOpen_twistCore_indexAt (-1) q₀.proj
  have hU : ∀ᶠ q in 𝓝 q₀, q.proj ∈ affineOpen i :=
    (FiberBundle.continuous_proj _ _).continuousAt.preimage_mem_nhds
      ((isOpen_affineOpen i).mem_nhds hi₀)
  have : MemTrivializationAtlas ((twistCore (𝕜 := 𝕜) (n := n) (-1)).localTriv i) := ⟨⟨i, rfl⟩⟩
  -- The coordinate of `q` in the chart `i` of `𝒪(-1)`.
  have h₁ : ContMDiffAt (𝓘(𝕜, Fin n → 𝕜).prod 𝓘(𝕜, 𝕜)) 𝓘(𝕜, 𝕜) r
      (fun q ↦ ((twistCore (𝕜 := 𝕜) (n := n) (-1)).localTriv i q).2) q₀ :=
    (contMDiffAt_snd.comp _ (((twistCore (-1)).localTriv i).contMDiffAt
      (((twistCore (-1)).mem_localTriv_source (i := i) q₀).2
        (by simpa [twistCore_baseSet] using hi₀)))).of_le le_top
  -- The representative `[1 : affineChart i ℓ]` of the line.
  have h₂ : ContMDiffAt (𝓘(𝕜, Fin n → 𝕜).prod 𝓘(𝕜, 𝕜)) 𝓘(𝕜, Fin (n + 1) → 𝕜) r
      (fun q : TotalSpace 𝕜 (twistCore (𝕜 := 𝕜) (n := n) (-1)).Fiber ↦
        Fin.insertNth (α := fun _ ↦ 𝕜) i 1 (affineChart i q.proj)) q₀ :=
    ((contMDiffOn_insertNth_affineChart i r).contMDiffAt
      ((isOpen_affineOpen i).mem_nhds hi₀)).comp _ (contMDiffAt_proj _)
  refine (h₁.smul h₂).congr_of_eventuallyEq (hU.mono fun q hq ↦ ?_)
  rw [Pi.smul_apply', insertNth_one_affineChart_eq_normalizedRep i hq]
  exact coe_tautologicalTwistCoreEquiv_symm_apply_of_mem hq q.snd

end Equiv

/-! ### The Euler class of `𝒪(-1)` -/

variable {n : ℕ}

/-- **The Euler class of `𝒪(0)` vanishes.** On `ℙ ℂ (Fin (n + 1) → ℂ)`, Tau Ceti's
`twistCore 0` is trivial, so its Euler class is zero. -/
theorem complexEulerClass_twistCore_zero :
    complexEulerClass (r := 0) ℂ (twistCore (𝕜 := ℂ) (n := n) 0).Fiber (finrank_self ℂ) = 0 := by
  refine complexEulerClass_eq_zero_of_forall_ne_zero ℂ _ (finrank_self ℂ)
    (s := fun _ ↦ ((1 : ℂ) : (twistCore (𝕜 := ℂ) (n := n) 0).Fiber _)) ?_
    fun _ ↦ one_ne_zero (α := ℂ)
  -- The section `1` read through the global trivialization of `𝒪(0)`.
  refine (continuousOn_univ.1 <| by
    simpa using (twistCoreZeroTrivialization (𝕜 := ℂ) (n := n)).continuousOn_symm_prodMk_left
      (v := (1 : ℂ))).congr fun b ↦ ?_
  have h := (twistCoreZeroTrivialization (𝕜 := ℂ) (n := n)).symm_apply_apply
    (x := TotalSpace.mk' ℂ b (1 : ℂ)) (by simp [Trivialization.mem_source])
  rw [twistCoreZeroTrivialization_apply] at h
  exact h

/-- **The Euler class of `𝒪(-1)`.** On `ℙ ℂ (Fin (n + 1) → ℂ)`, the Euler class of Tau Ceti's
`twistCore (-1)`, read in integral cohomology through `TopCat.uliftIntegralCohomologyIso`, is minus
the hyperplane class, since `twistCore (-1)` is the tautological line. -/
theorem complexEulerClass_twistCore_neg_one :
    ((TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))).uliftIntegralCohomologyIso 2).hom
        (complexEulerClass (r := 0) ℂ (twistCore (𝕜 := ℂ) (n := n) (-1)).Fiber
          (finrank_self ℂ)) =
      -hyperplaneClass (Fin (n + 1) → ℂ) := by
  rw [hyperplaneClass_def, neg_neg, complexEulerClass_eq_of_fiberwise (F := ℂ)
    (E := Tautological ℂ (Fin (n + 1) → ℂ)) (finrank_self ℂ) (finrank_self ℂ)
    (φ := fun x ↦ (tautologicalTwistCoreEquiv x).symm) continuous_tautologicalTwistCoreEquiv_symm]

end Projectivization

end
