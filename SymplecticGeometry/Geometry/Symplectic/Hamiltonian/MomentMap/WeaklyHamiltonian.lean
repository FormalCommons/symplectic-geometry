/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Algebra
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap
import Mathlib.LinearAlgebra.Basis.VectorSpace
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.Manifold
import TauCeti.Geometry.Manifold.MFDeriv.Constancy

/-!
# Moment maps of weakly Hamiltonian actions

Let `a : Z ↦ Z_M` be an infinitesimal action of a real Lie algebra `𝔤` on a manifold `M` with a
two-form `σ`, for instance the fundamental vector fields `TauCeti.InfinitesimalAction.fundamental`
of a smooth action of a Lie group. The action is *weakly Hamiltonian* when every `Z_M` is the
Hamiltonian vector field of some smooth function. A moment map asks for more: a choice of these
functions depending linearly on `Z`. This file shows that the two notions agree, and describes the
freedom in the choice.

* `TauCeti.SmoothTwoForm.exists_isMomentMap_iff`: a moment map of `a` exists exactly when every
  `Z_M` has a smooth Hamiltonian. The smooth Hamiltonians of the vector fields `Z_M` form a
  subspace of `𝔤 × (M → ℝ)` that projects onto `𝔤`, and a linear section of that projection, which
  exists over a field, is a moment map. Choosing the section on a basis of `𝔤` is the classical
  argument. No dimension hypothesis on `𝔤` is needed, nor that `σ` be closed or nondegenerate.
* `TauCeti.SmoothTwoForm.IsMomentMap.isMomentMap_iff_exists_eq_add_locallyConstant`: given one
  moment map `μ`, the moment maps of `a` are exactly the maps `x ↦ μ x + c(·) x` for a linear map
  `c : 𝔤 → LocallyConstant M ℝ`. On a preconnected manifold the locally constant functions are the
  constants, and this is Tau Ceti's
  `TauCeti.SmoothTwoForm.IsMomentMap.isMomentMap_iff_exists_eq_add`. For a finite-dimensional
  `𝔤`, it follows that two moment maps of `a` agree on a clopen set
  (`TauCeti.SmoothTwoForm.IsMomentMap.isClopen_setOfPred_eq`).

Both results are stated in Tau Ceti's convention `ι_{Z_M} σ = d⟨μ, Z⟩`. They hold unchanged in the
opposite convention `ι_{Z_M} σ = -d⟨μ, Z⟩`, since passing from one convention to the other replaces
`μ` by `-μ` and keeps the class of moment maps and of locally constant shifts.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.2
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {σ : SmoothTwoForm I M} {a : InfinitesimalAction 𝔤 I M} {μ μ' : M → Module.Dual ℝ 𝔤}

/-- The pairs `(Z, f)` such that `f` is a smooth Hamiltonian of the vector field `Z_M`, a
subspace of `𝔤 × (M → ℝ)`. -/
private def hamiltonianPairs (σ : SmoothTwoForm I M) (a : InfinitesimalAction 𝔤 I M) :
    Submodule ℝ (𝔤 × (M → ℝ)) where
  carrier := {p | ContMDiff I 𝓘(ℝ) ∞ p.2 ∧ σ.IsHamiltonianVectorField p.2 (a p.1)}
  add_mem' {p q} hp hq := by
    refine ⟨hp.1.add hq.1, ?_⟩
    rw [Prod.snd_add, Prod.fst_add, map_add]
    exact hp.2.add hq.2 (hp.1.mdifferentiable (by simp)) (hq.1.mdifferentiable (by simp))
  zero_mem' := by
    refine ⟨contMDiff_const, ?_⟩
    rw [Prod.snd_zero, Prod.fst_zero, map_zero]
    exact isHamiltonianVectorField_const 0
  smul_mem' c p hp := by
    refine ⟨(contMDiff_const : ContMDiff I 𝓘(ℝ) ∞ fun _ : M ↦ c).smul hp.1, ?_⟩
    rw [Prod.smul_snd, Prod.smul_fst, map_smul]
    exact hp.2.const_smul c

/-- **Moment maps of weakly Hamiltonian actions.** An infinitesimal action `a : Z ↦ Z_M` of a real
Lie algebra on a manifold with a two-form `σ` has a moment map exactly when every vector field
`Z_M` is the Hamiltonian vector field of a smooth function: the Hamiltonians can then be chosen
to depend linearly on `Z`. -/
theorem exists_isMomentMap_iff :
    (∃ μ : M → Module.Dual ℝ 𝔤, σ.IsMomentMap a μ) ↔
      ∀ Z, ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ f ∧ σ.IsHamiltonianVectorField f (a Z) := by
  refine ⟨fun ⟨μ, h⟩ Z ↦ ⟨fun x ↦ μ x Z, h.contMDiff Z, h.isHamiltonianVectorField Z⟩,
    fun h ↦ ?_⟩
  let π := (LinearMap.fst ℝ 𝔤 (M → ℝ)).comp (hamiltonianPairs σ a).subtype
  have hπ : LinearMap.range π = ⊤ := LinearMap.range_eq_top.2 fun Z ↦
    have ⟨f, hf⟩ := h Z
    ⟨⟨(Z, f), hf⟩, rfl⟩
  obtain ⟨s, hs⟩ := π.exists_rightInverse_of_surjective hπ
  have hsZ (Z : 𝔤) : (s Z : 𝔤 × (M → ℝ)).1 = Z := LinearMap.congr_fun hs Z
  refine ⟨fun x ↦ (LinearMap.proj x ∘ₗ LinearMap.snd ℝ 𝔤 (M → ℝ) ∘ₗ
    (hamiltonianPairs σ a).subtype) ∘ₗ s, fun Z ↦ (s Z).property.1, fun Z ↦ ?_⟩
  have := (s Z).property.2
  rwa [hsZ] at this

namespace IsMomentMap

/-- Adding to a moment map `μ` a linear map `c` from the Lie algebra to the locally constant
functions on `M` gives a moment map `x ↦ μ x + c(·) x` of the same action. -/
theorem add_locallyConstant (h : σ.IsMomentMap a μ) (c : 𝔤 →ₗ[ℝ] LocallyConstant M ℝ) :
    σ.IsMomentMap a fun x ↦ μ x + LocallyConstant.evalₗ ℝ x ∘ₗ c := by
  have hμ (Z : 𝔤) : (fun x ↦ (μ x + LocallyConstant.evalₗ ℝ x ∘ₗ c) Z) = (fun x ↦ μ x Z) + c Z :=
    funext fun x ↦ by simp
  have hc (Z : 𝔤) : ContMDiff I 𝓘(ℝ) ∞ (c Z) := (c Z).isLocallyConstant.contMDiff
  refine ⟨fun Z ↦ hμ Z ▸ (h.contMDiff Z).add (hc Z), fun Z ↦ ?_⟩
  rw [hμ Z, ← add_zero (a Z)]
  exact (h.isHamiltonianVectorField Z).add
    (isHamiltonianVectorField_zero_of_isLocallyConstant (c Z).isLocallyConstant)
    (fun x ↦ h.mdifferentiableAt Z x) ((hc Z).mdifferentiable (by simp))

/-- **Moment maps up to locally constant shifts.** If `μ` is a moment map of an infinitesimal
action, the moment maps of the same action are exactly the maps `x ↦ μ x + c(·) x` for a linear
map `c` from the Lie algebra to the locally constant functions on `M`. -/
theorem isMomentMap_iff_exists_eq_add_locallyConstant (h : σ.IsMomentMap a μ) :
    σ.IsMomentMap a μ' ↔
      ∃ c : 𝔤 →ₗ[ℝ] LocallyConstant M ℝ, ∀ x Z, μ' x Z = μ x Z + c Z x := by
  constructor
  · intro h'
    -- The difference of the two moment maps, component by component.
    let c : 𝔤 →ₗ[ℝ] LocallyConstant M ℝ :=
      { toFun Z := ⟨fun x ↦ μ' x Z - μ x Z,
          MDifferentiable.isLocallyConstant_of_mfderiv_eq_zero
            (fun x ↦ (h'.mdifferentiableAt Z x).sub (h.mdifferentiableAt Z x))
            (h.mfderiv_sub_eq_zero h' Z)⟩
        map_add' Z Z' := by ext x; simp; ring
        map_smul' r Z := by ext x; simp; ring }
    exact ⟨c, fun x Z ↦ by simp [c]⟩
  · rintro ⟨c, hc⟩
    have hμ' : μ' = fun x ↦ μ x + LocallyConstant.evalₗ ℝ x ∘ₗ c :=
      funext fun x ↦ LinearMap.ext fun Z ↦ hc x Z
    exact hμ' ▸ h.add_locallyConstant c

/-- Two moment maps of the same infinitesimal action of a finite-dimensional Lie algebra agree on
a clopen set. -/
theorem isClopen_setOfPred_eq [FiniteDimensional ℝ 𝔤] (h : σ.IsMomentMap a μ)
    (h' : σ.IsMomentMap a μ') : IsClopen {x | μ x = μ' x} := by
  obtain ⟨c, hc⟩ := h.isMomentMap_iff_exists_eq_add_locallyConstant.1 h'
  let b := Module.finBasis ℝ 𝔤
  have : {x | μ x = μ' x} = ⋂ i, {x | c (b i) x = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    refine ⟨fun hx i ↦ ?_, fun hx ↦ b.ext fun i ↦ ?_⟩
    · have := hc x (b i)
      rw [← hx] at this
      linarith
    · rw [hc, hx i, add_zero]
  rw [this]
  exact isClopen_iInter_of_finite fun i ↦ (c (b i)).isLocallyConstant.isClopen_fiber 0

end IsMomentMap

end TauCeti.SmoothTwoForm

end
