/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CommutingFlow
public import TauCeti.Geometry.Symplectic.Hamiltonian.ExtendedPhaseSpace.Manifold
public import TauCeti.Geometry.Symplectic.Hamiltonian.LieAlgebra
public import Mathlib.Algebra.Lie.Quotient
import SymplecticGeometry.Algebra.Lie.Quotient
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Flow.Family

/-!
# Hamiltonian flows and the Poisson algebra of a symplectic manifold

Let `σ` be a two-form on a manifold `M`, with Hamiltonian vector fields `ι_{X_f} σ = df` and
Poisson bracket `{f, g} = σ(X_f, X_g)` as in Tau Ceti
(`TauCeti.SmoothTwoForm.hamiltonianVectorField`, `TauCeti.SmoothTwoForm.poissonBracket`). This
file adds what Tau Ceti lacks to show that the smooth functions on a symplectic manifold form a
Poisson algebra on which Hamiltonian flows act, and collects the whole statement in one theorem.
The Leibniz rule of the bracket is Tau Ceti's `TauCeti.SmoothTwoForm.poissonBracket_mul_left`.

* The **kernel of `f ↦ -X_f`** on the Poisson Lie algebra of a symplectic form consists of the
  locally constant functions
  (`TauCeti.SmoothTwoForm.mem_ker_negHamiltonianLieHom_iff_isLocallyConstant`), and of the
  constant functions when `M` is preconnected
  (`TauCeti.SmoothTwoForm.mem_ker_negHamiltonianLieHom_iff_exists_eq_const`). The quotient by it
  is isomorphic to the Lie algebra of Hamiltonian vector fields
  (`TauCeti.SmoothTwoForm.negHamiltonianLieHomQuotKerEquiv`), by the first isomorphism theorem
  `LieHom.quotKerEquivRange` and Tau Ceti's `TauCeti.SmoothTwoForm.range_negHamiltonianLieHom`.

The main theorem, `TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlow_and_poissonAlgebra`,
collects these results with Tau Ceti's: existence, uniqueness and smoothness of `X_f`;
preservation of `σ` and of `f` by the local flow of `X_f`; preservation of `σ` by local
time-dependent Hamiltonian flows and the energy identity `d/dt H_t(φ_t q) = (∂_t H_t)(φ_t q)`;
smoothness, bilinearity, skew-symmetry, the Jacobi identity and the Leibniz rule of the bracket;
`X_{{f, g}} = -[X_f, X_g]`, where `-[X, Y]` with Mathlib's bracket `VectorField.mlieBracket` is
the bracket of McDuff–Salamon; naturality of `X_f` under symplectomorphisms; and the kernel and
quotient of `f ↦ -X_f`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.1,
  Proposition 3.1.10 and the discussion around it.
-/

public section

noncomputable section

open Bundle VectorField
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace SmoothTwoForm

variable {σ : SmoothTwoForm I M} {f g k : M → ℝ} {x : M}

/-! ### The kernel of `f ↦ -X_f` -/

variable [FiniteDimensional ℝ E]

/-- **The kernel of `f ↦ -X_f`** consists of the locally constant smooth functions. -/
theorem mem_ker_negHamiltonianLieHom_iff_isLocallyConstant (hσ : σ.IsSymplectic)
    {f : σ.PoissonLieAlgebra hσ} :
    f ∈ (σ.negHamiltonianLieHom hσ).ker ↔ IsLocallyConstant (σ.poissonLieAlgebraEquiv hσ f) := by
  have hf : MDifferentiable I 𝓘(ℝ) (σ.poissonLieAlgebraEquiv hσ f) :=
    (σ.poissonLieAlgebraEquiv hσ f).contMDiff.mdifferentiable (by simp)
  rw [mem_ker_negHamiltonianLieHom_iff, ← mextDeriv_ofFunction_eq_zero_iff hf, funext_iff]
  refine forall_congr' fun x ↦ ?_
  rw [Pi.zero_apply, mextDeriv_ofFunction_apply_eq_zero_iff, mvfderiv_eq_zero_iff]

/-- On a preconnected manifold, the kernel of `f ↦ -X_f` consists of the constant functions. -/
theorem mem_ker_negHamiltonianLieHom_iff_exists_eq_const [PreconnectedSpace M]
    (hσ : σ.IsSymplectic) {f : σ.PoissonLieAlgebra hσ} :
    f ∈ (σ.negHamiltonianLieHom hσ).ker ↔
      ∃ c : ℝ, ⇑(σ.poissonLieAlgebraEquiv hσ f) = fun _ ↦ c := by
  rw [mem_ker_negHamiltonianLieHom_iff_isLocallyConstant]
  exact ⟨IsLocallyConstant.exists_eq_const, fun ⟨c, hc⟩ ↦ hc ▸ IsLocallyConstant.const c⟩

variable (σ) in
/-- The quotient of the Poisson Lie algebra of a symplectic form by the kernel of `f ↦ -X_f` is
isomorphic, as a Lie algebra, to the Lie algebra of Hamiltonian vector fields, by the class of
`f` going to `-X_f` (`TauCeti.SmoothTwoForm.coe_negHamiltonianLieHomQuotKerEquiv_mk`). On a
preconnected manifold the kernel is the constant functions
(`TauCeti.SmoothTwoForm.mem_ker_negHamiltonianLieHom_iff_exists_eq_const`). -/
def negHamiltonianLieHomQuotKerEquiv (hσ : σ.IsSymplectic) :
    (σ.PoissonLieAlgebra hσ ⧸ (σ.negHamiltonianLieHom hσ).ker) ≃ₗ⁅ℝ⁆
      (σ.hamiltonianLieIdeal hσ.isClosed).toLieSubalgebra :=
  (σ.negHamiltonianLieHom hσ).quotKerEquivRange.trans
    (LieEquiv.ofEq _ _ (congrArg _ (range_negHamiltonianLieHom hσ)))

theorem negHamiltonianLieHomQuotKerEquiv_def (hσ : σ.IsSymplectic) :
    σ.negHamiltonianLieHomQuotKerEquiv hσ = (σ.negHamiltonianLieHom hσ).quotKerEquivRange.trans
      (LieEquiv.ofEq _ _ (congrArg _ (range_negHamiltonianLieHom hσ))) :=
  (rfl)

/-- The isomorphism `TauCeti.SmoothTwoForm.negHamiltonianLieHomQuotKerEquiv` sends the class of
`f` to `-X_f`. -/
@[simp]
theorem coe_negHamiltonianLieHomQuotKerEquiv_mk (hσ : σ.IsSymplectic)
    (f : σ.PoissonLieAlgebra hσ) :
    (σ.negHamiltonianLieHomQuotKerEquiv hσ (LieSubmodule.Quotient.mk f) :
      σ.symplecticLieSubalgebra hσ.isClosed) = σ.negHamiltonianLieHom hσ f := by
  rw [negHamiltonianLieHomQuotKerEquiv_def, LieEquiv.trans_apply, LieEquiv.ofEq_apply,
    LieHom.coe_quotKerEquivRange_mk]


/-! ### The milestone -/

namespace IsSymplectic

/-- **Hamiltonian flows and the Poisson algebra.** Let `σ` be a symplectic form on a
finite-dimensional manifold `M` without boundary.

* Every smooth `f` has a unique Hamiltonian vector field `X_f`, with `ι_{X_f} σ = df`, and `X_f`
  is smooth.
* The local flow of `X_f` preserves `σ` and `f` wherever it is defined.
* For a smooth time-dependent Hamiltonian `H`, the local time-dependent flow `φ` of the fields
  `X_{H_t}` preserves `σ` wherever it is defined, and satisfies the energy identity
  `d/du H_u(φ_{s,u} x) = (∂_t H_t)(φ_{s,t} x)` at `u = t`.
* The bracket `{f, g} = σ(X_f, X_g) = df(X_g)` of smooth functions is smooth; on smooth
  functions it is linear in each argument and antisymmetric, and the Jacobi identity and the
  Leibniz rule hold for it.
* `X_{{f, g}} = -[X_f, X_g]` for Mathlib's bracket `VectorField.mlieBracket`; that is,
  `X_{{f, g}}` is the bracket of `X_f` and `X_g` in McDuff–Salamon's convention.
* For a symplectomorphism `χ`, `dχ_q (X_{f ∘ χ}(q)) = X_f(χ q)`, that is `X_{f ∘ χ} = χ^* X_f`.
* The kernel of `f ↦ -X_f`, on the Poisson Lie algebra, is the locally constant functions, and
  the constant functions if `M` is preconnected. The class of `f` going to `-X_f` is an
  isomorphism `TauCeti.SmoothTwoForm.negHamiltonianLieHomQuotKerEquiv` of the quotient onto the
  Lie algebra of Hamiltonian vector fields; the sign is there because that Lie algebra carries
  Mathlib's bracket, so that `f ↦ X_f` reverses brackets.

Milestone: *Hamiltonian flows and the Poisson algebra*. -/
theorem hamiltonianFlow_and_poissonAlgebra [I.Boundaryless] [T2Space M] (hσ : σ.IsSymplectic) :
    (∀ f : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ f →
      σ.IsHamiltonianVectorField f (σ.hamiltonianVectorField f) ∧
      (∀ X : (x : M) → TangentSpace I x,
        σ.IsHamiltonianVectorField f X ↔ X = σ.hamiltonianVectorField f) ∧
      ContMDiff I I.tangent ∞ (T% (σ.hamiltonianVectorField f))) ∧
    (∀ f : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ f → ∀ t x, (t, x) ∈ flowDomain (σ.hamiltonianVectorField f) →
      TauCeti.mpullback I I (flowOf (σ.hamiltonianVectorField f) t) σ.val x = σ.val x ∧
        f (flowOf (σ.hamiltonianVectorField f) t x) = f x) ∧
    (∀ H : ℝ → M → ℝ, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ (Function.uncurry H) → ∀ s t x,
      ((s, t), x) ∈ timeDependentFlowDomain (fun u ↦ σ.hamiltonianVectorField (H u)) →
      TauCeti.mpullback I I (timeDependentFlowOf (fun u ↦ σ.hamiltonianVectorField (H u)) s t)
          σ.val x = σ.val x ∧
        HasDerivAt
          (fun u ↦ H u (timeDependentFlowOf (fun u ↦ σ.hamiltonianVectorField (H u)) s u x))
          (deriv (fun u ↦
            H u (timeDependentFlowOf (fun u ↦ σ.hamiltonianVectorField (H u)) s t x)) t) t) ∧
    (∀ f g k : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ f → ContMDiff I 𝓘(ℝ) ∞ g → ContMDiff I 𝓘(ℝ) ∞ k →
      ContMDiff I 𝓘(ℝ) ∞ (σ.poissonBracket f g) ∧ ∀ (c : ℝ) (x : M),
      σ.poissonBracket f g x = mvfderiv I f x (σ.hamiltonianVectorField g x) ∧
      σ.poissonBracket (f + g) k x = σ.poissonBracket f k x + σ.poissonBracket g k x ∧
      σ.poissonBracket k (f + g) x = σ.poissonBracket k f x + σ.poissonBracket k g x ∧
      σ.poissonBracket (c • f) g x = c * σ.poissonBracket f g x ∧
      σ.poissonBracket f (c • g) x = c * σ.poissonBracket f g x ∧
      σ.poissonBracket f g x = -σ.poissonBracket g f x ∧
      σ.poissonBracket f (σ.poissonBracket g k) x + σ.poissonBracket g (σ.poissonBracket k f) x +
        σ.poissonBracket k (σ.poissonBracket f g) x = 0 ∧
      σ.poissonBracket (f * g) k x =
        f x * σ.poissonBracket g k x + g x * σ.poissonBracket f k x) ∧
    (∀ f g : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ f → ContMDiff I 𝓘(ℝ) ∞ g →
      σ.hamiltonianVectorField (σ.poissonBracket f g) =
        -mlieBracket I (σ.hamiltonianVectorField f) (σ.hamiltonianVectorField g)) ∧
    (∀ χ ∈ SmoothForm.diffeomorphStabilizer σ, ∀ f : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ f → ∀ q : M,
      mfderiv I I χ q (σ.hamiltonianVectorField (f ∘ χ) q) = σ.hamiltonianVectorField f (χ q)) ∧
    (∀ f : σ.PoissonLieAlgebra hσ,
      f ∈ (σ.negHamiltonianLieHom hσ).ker ↔ IsLocallyConstant (σ.poissonLieAlgebraEquiv hσ f)) ∧
    (PreconnectedSpace M → ∀ f : σ.PoissonLieAlgebra hσ, f ∈ (σ.negHamiltonianLieHom hσ).ker ↔
      ∃ c : ℝ, ⇑(σ.poissonLieAlgebraEquiv hσ f) = fun _ ↦ c) ∧
    (∀ f : σ.PoissonLieAlgebra hσ,
      (σ.negHamiltonianLieHomQuotKerEquiv hσ (LieSubmodule.Quotient.mk f) :
        σ.symplecticLieSubalgebra hσ.isClosed) = σ.negHamiltonianLieHom hσ f) := by
  have hnd := hσ.isNondegenerate
  have hX2 {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
      ContMDiff I I.tangent 2 (fun y ↦ (⟨y, σ.hamiltonianVectorField f y⟩ : TangentBundle I M)) :=
    hnd.contMDiff_hamiltonianVectorField (by simp) (hf.of_le (by simp))
  have hv {H : ℝ → M → ℝ} (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ (Function.uncurry H)) :
      ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
        (fun p : ℝ × M ↦ (⟨p.2, σ.hamiltonianVectorField (H p.1) p.2⟩ : TangentBundle I M)) :=
    hnd.contMDiff_hamiltonianVectorField_uncurry (by simp) (hH.of_le (by simp))
  have hmd {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M) : MDifferentiableAt I 𝓘(ℝ) f x :=
    hf.mdifferentiableAt (by simp)
  refine ⟨fun f hf ↦ ⟨hnd.isHamiltonianVectorField_hamiltonianVectorField f,
      fun X ↦ hnd.isHamiltonianVectorField_iff_eq,
      hnd.contMDiff_hamiltonianVectorField le_rfl (hf.of_le (by simp))⟩,
    fun f hf t x hx ↦ ⟨?_, ?_⟩, fun H hH s t x hx ↦ ⟨?_, ?_⟩,
    fun f g k hf hg hk ↦ ⟨hnd.contMDiff_poissonBracket le_rfl (hf.of_le (by simp))
      (hg.of_le (by simp)), fun c x ↦
        ⟨σ.poissonBracket_eq_mvfderiv f g x, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩,
    fun f g hf hg ↦ ?_, fun χ hχ f hf q ↦ ?_,
    fun f ↦ mem_ker_negHamiltonianLieHom_iff_isLocallyConstant hσ,
    fun _ f ↦ mem_ker_negHamiltonianLieHom_iff_exists_eq_const hσ,
    fun f ↦ coe_negHamiltonianLieHomQuotKerEquiv_mk hσ f⟩
  · exact (hnd.isHamiltonianVectorField_hamiltonianVectorField f).mpullback_flowOf_apply
      hσ.isClosed (hf.of_le (by simp)) ((hX2 hf).of_le one_le_two) hx
  · rw [flowOf_apply]
    exact (isFirstIntegral_self f).apply_maximalIntegralCurve hnd (hf.of_le (by simp))
      (hf.mdifferentiable (by simp)) (mem_flowDomain.1 hx)
  · exact mpullback_timeDependentFlowOf_apply_of_isHamiltonianVectorField
      (fun u _ ↦ hnd.isHamiltonianVectorField_hamiltonianVectorField (H u)) hσ.isClosed
      (fun u _ ↦ (hH.comp (contMDiff_const.prodMk contMDiff_id)).of_le (by simp)) (hv hH) hx
  · exact IsHamiltonianVectorField.hasDerivAt_apply_self_of_hasMFDerivAt
      (X := fun u ↦ σ.hamiltonianVectorField (H u))
      (hnd.isHamiltonianVectorField_hamiltonianVectorField (H t)) (hH.mdifferentiableAt (by simp))
      (hasMFDerivAt_timeDependentFlowOf ((hv hH).of_le one_le_two) hx)
  · exact poissonBracket_add_left (hmd hf x) (hmd hg x)
  · exact poissonBracket_add_right (hmd hf x) (hmd hg x)
  · exact poissonBracket_const_smul_left c x
  · exact poissonBracket_const_smul_right c x
  · exact (neg_poissonBracket σ f g x).symm
  · exact hnd.poissonBracket_jacobi hσ.isClosed (hf.of_le (by simp)) (hg.of_le (by simp))
      (hk.of_le (by simp)) x
  · exact poissonBracket_mul_left (hmd hf x) (hmd hg x)
  · exact hnd.hamiltonianVectorField_poissonBracket hσ.isClosed (hf.of_le (by simp))
      (hg.of_le (by simp))
  · exact hnd.mfderiv_hamiltonianVectorField_comp hnd χ.contMDiff
      (SmoothForm.mem_diffeomorphStabilizer.1 hχ)
      (hnd.surjective_of_eval₂_map (SmoothForm.eval₂_mfderiv_of_mem_diffeomorphStabilizer hχ _))
      (hmd hf _)

end IsSymplectic

end SmoothTwoForm

end TauCeti
