/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cayley.Smooth
public import TauCeti.Geometry.Symplectic.SymplecticTransport
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic.NoncommRing
import SymplecticGeometry.Topology.Compactness.Compact

/-!
# The domain of the Cayley path

For `A B` in a ring `R` over `ℝ`, Tau Ceti's Cayley path
`TauCeti.cayleyPathFormula b A B = A (1 + b C)(1 - b C)⁻¹`, with
`C = TauCeti.cayleyFormula A B = -(1 + A B)(1 - A B)⁻¹`, involves two inverses. This file names
the set of triples `(b, A, B)` where both `1 - A B` and `1 - b C` are units, and shows that in a
complete normed `ℝ`-algebra it is open and the Cayley path is smooth on it. The pairs `(A, B)`
for which the whole segment `b ∈ [0, 1]` lies in it form an open set too, by compactness of
`[0, 1]`. For a compatible `J₀` and a tame `J`, every `|b| ≤ 1` gives a point of the domain, and
the path from `J₀` to `J` stays among the tame structures, and among the compatible ones when `J`
is compatible. Both facts hold on any topological vector space isomorphic to a
finite-dimensional normed space, such as a fibre of a vector bundle.

## Main definitions and results

* `SymplecticGeometry.cayleyDomain R`: the triples where both denominators are units.
* `SymplecticGeometry.map_mem_cayleyDomain_iff`: algebra isomorphisms preserve the domain.
* `TauCeti.cayleyPathFormula_zero`, `TauCeti.cayleyPathFormula_one`: the two ends of the path, and
  `TauCeti.cayleyPathFormula_self`: the path from a square root of `-1` to itself is constant.
* `TauCeti.contDiffAt_cayleyFormula`: the Cayley coordinate is smooth, jointly in both
  arguments, wherever `1 - A B` is a unit.
* `SymplecticGeometry.isOpen_cayleyDomain`, `SymplecticGeometry.contDiffOn_cayleyPathFormula`.
* `SymplecticGeometry.isOpen_setOfPred_forall_Icc_mem_cayleyDomain`: the pairs `(A, B)` whose
  segment over `[0, 1]` lies in the domain form an open set.
* `TauCeti.SymplecticForm.Compatible.mem_cayleyDomain`: a compatible and a tame structure,
  with `|b| ≤ 1`, give a point of the domain, and
  `TauCeti.SymplecticForm.Compatible.mem_cayleyDomain_of_continuousLinearEquiv` does so on a
  space isomorphic to a finite-dimensional normed space.
* `TauCeti.SymplecticForm.Compatible.exists_toLinearMap_eq_cayleyPathFormula`: on such a space,
  the Cayley path represents a tame structure, and a compatible one when its endpoint is.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 2.5.13 (the Cayley transform proof of Sévennec).
-/

public section

open Set Topology

namespace TauCeti

section Ring

variable {R : Type*} [Ring R] [Algebra ℝ R]
/-- At the coefficient `0` the Cayley path is at its starting point `A`. -/
@[simp]
theorem cayleyPathFormula_zero (A B : R) : cayleyPathFormula 0 A B = A := by
  simp [cayleyPathFormula_def]

/-- At the coefficient `1` the Cayley path from a square root `A` of `-1` reaches `B`, whenever
`1 - A B` is a unit. -/
theorem cayleyPathFormula_one {A B : R} (hA : A * A = -1) (h : IsUnit (1 - A * B)) :
    cayleyPathFormula 1 A B = B := by
  set D := 1 - A * B with hD
  have h₁ : (1 : R) + cayleyFormula A B = -(2 : ℝ) • (A * B) * Ring.inverse D := by
    rw [cayleyFormula_def, ← hD]
    nth_rewrite 1 [← Ring.mul_inverse_cancel D h]
    rw [hD]
    simp only [two_smul, neg_smul]
    noncomm_ring
  have h₂ : (1 : R) - cayleyFormula A B = (2 : ℝ) • Ring.inverse D := by
    rw [cayleyFormula_def, ← hD]
    nth_rewrite 1 [← Ring.mul_inverse_cancel D h]
    rw [hD]
    simp only [two_smul]
    noncomm_ring
  -- `1 - C = 2 D⁻¹` is a unit, with inverse `D / 2`.
  let u : Rˣ := ⟨(2 : ℝ) • Ring.inverse D, (2⁻¹ : ℝ) • D,
    by rw [smul_mul_smul_comm, Ring.inverse_mul_cancel D h]; norm_num,
    by rw [smul_mul_smul_comm, Ring.mul_inverse_cancel D h]; norm_num⟩
  rw [cayleyPathFormula_def, one_smul, h₁, h₂, show Ring.inverse ((2 : ℝ) • Ring.inverse D) =
    (2⁻¹ : ℝ) • D from Ring.inverse_unit u]
  calc A * (-(2 : ℝ) • (A * B) * Ring.inverse D) * ((2⁻¹ : ℝ) • D)
      = -((2⁻¹ : ℝ) * 2) • (A * A * B * (Ring.inverse D * D)) := by
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc, neg_smul, neg_mul,
          mul_neg, smul_neg]
    _ = B := by
        rw [Ring.inverse_mul_cancel D h, hA]
        norm_num

/-- The Cayley path from a square root `A` of `-1` to itself is constant at `A`. -/
@[simp]
theorem cayleyPathFormula_self {A : R} (hA : A * A = -1) (b : ℝ) :
    cayleyPathFormula b A A = A := by
  simp [cayleyPathFormula_def, cayleyFormula_def, hA]

end Ring

section Normed

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

/-- The Cayley coordinate `cayleyFormula A B` is smooth, jointly in `A` and `B`, at every pair
with `1 - A B` a unit. -/
theorem contDiffAt_cayleyFormula {n : WithTop ℕ∞} {A B : R} (h : IsUnit (1 - A * B)) :
    ContDiffAt ℝ n (fun p : R × R ↦ cayleyFormula p.1 p.2) (A, B) := by
  have hAB : ContDiffAt ℝ n (fun p : R × R ↦ p.1 * p.2) (A, B) :=
    contDiffAt_fst.mul contDiffAt_snd
  simp only [cayleyFormula_def]
  exact ((contDiffAt_const.add hAB).mul ((contDiffAt_const.sub hAB).inverse h)).neg

end Normed

end TauCeti

namespace SymplecticGeometry

open TauCeti

section Ring

variable (R : Type*) [Ring R] [Algebra ℝ R]

/-- The triples `(b, A, B)` at which both denominators of the Cayley path
`cayleyPathFormula b A B` are units: `1 - A B`, and `1 - b C` for the Cayley coordinate
`C = cayleyFormula A B`. -/
def cayleyDomain : Set (ℝ × R × R) :=
  {q | IsUnit (1 - q.2.1 * q.2.2) ∧ IsUnit (1 - q.1 • cayleyFormula q.2.1 q.2.2)}

variable {R}

@[simp]
lemma mem_cayleyDomain {q : ℝ × R × R} :
    q ∈ cayleyDomain R ↔
      IsUnit (1 - q.2.1 * q.2.2) ∧ IsUnit (1 - q.1 • cayleyFormula q.2.1 q.2.2) :=
  Iff.rfl

/-- An algebra isomorphism `f` maps the domain of the Cayley path onto the domain of the Cayley
path: `(b, f A, f B)` lies in it exactly when `(b, A, B)` does. -/
theorem map_mem_cayleyDomain_iff {S E : Type*} [Ring S] [Algebra ℝ S] [EquivLike E R S]
    [AlgEquivClass E ℝ R S] (f : E) {b : ℝ} {A B : R} :
    (b, f A, f B) ∈ cayleyDomain S ↔ (b, A, B) ∈ cayleyDomain R := by
  simp only [mem_cayleyDomain, ← map_mul, ← map_one f, ← map_sub, ← map_cayleyFormula,
    ← map_smul, isUnit_map_iff]

end Ring

section Normed

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

variable (R) in
/-- The domain of the Cayley path is open. -/
theorem isOpen_cayleyDomain : IsOpen (cayleyDomain R) := by
  have hs : IsOpen {q : ℝ × R × R | IsUnit (1 - q.2.1 * q.2.2)} :=
    Units.isOpen.preimage (by fun_prop)
  have hf : ContinuousOn (fun q : ℝ × R × R ↦ 1 - q.1 • cayleyFormula q.2.1 q.2.2)
      {q | IsUnit (1 - q.2.1 * q.2.2)} := by
    rintro ⟨b, A, B⟩ h
    have hC : ContinuousAt (fun q : ℝ × R × R ↦ cayleyFormula q.2.1 q.2.2) (b, A, B) :=
      (contDiffAt_cayleyFormula (n := 0) h).continuousAt.comp_of_eq continuousAt_snd rfl
    exact (continuousAt_const.sub (continuousAt_fst.smul hC)).continuousWithinAt
  exact hf.isOpen_inter_preimage hs Units.isOpen

/-- The Cayley path is smooth, jointly in the parameter and both endpoints, on its domain. -/
theorem contDiffOn_cayleyPathFormula {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (fun q : ℝ × R × R ↦ cayleyPathFormula q.1 q.2.1 q.2.2) (cayleyDomain R) :=
  fun _ hq ↦ (contDiffAt_cayleyPathFormula hq.1 hq.2).contDiffWithinAt

variable (R) in
/-- The pairs `(A, B)` such that `(b, A, B)` lies in the domain of the Cayley path for every
`b ∈ [0, 1]` form an open set. -/
theorem isOpen_setOfPred_forall_Icc_mem_cayleyDomain :
    IsOpen {p : R × R | ∀ b ∈ Icc (0 : ℝ) 1, (b, p.1, p.2) ∈ cayleyDomain R} :=
  isCompact_Icc.isOpen_setOfPred_forall_prodMk_mem <| (isOpen_cayleyDomain R).preimage
    (by fun_prop : Continuous fun z : (R × R) × ℝ ↦ (z.2, z.1.1, z.1.2))

end Normed

end SymplecticGeometry

namespace TauCeti.SymplecticForm

open SymplecticGeometry

section NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ J : AlmostComplexStructure V}

/-- For an `ω`-compatible `J₀`, an `ω`-tame `J` and `|b| ≤ 1`, the triple of `b` and continuous
endomorphisms representing `J₀` and `J` lies in the domain of the Cayley path. -/
theorem Compatible.mem_cayleyDomain (h₀ : ω.Compatible J₀) (h : ω.Tames J) {b : ℝ}
    (hb : |b| ≤ 1) {A B : V →L[ℝ] V} (hA : A.toLinearMap = J₀.toLinearMap)
    (hB : B.toLinearMap = J.toLinearMap) :
    (b, A, B) ∈ cayleyDomain (V →L[ℝ] V) :=
  ⟨h₀.tames.isUnit_one_sub_mul_of_toLinearMap h hA hB,
    h₀.isUnit_one_sub_smul_cayleyFormula h hb hA hB⟩

end NormedSpace

section ContinuousLinearEquiv

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {ω : SymplecticForm W} {J₀ J : AlmostComplexStructure W} {A B : W →L[ℝ] W}

/-- Let `W` be a topological vector space isomorphic to a finite-dimensional normed space, `ω` a
symplectic form on `W`, `J₀` an `ω`-compatible and `J` an `ω`-tame complex structure, represented
by continuous endomorphisms `A` and `B`. Then for every `|b| ≤ 1` the triple `(b, A, B)` lies in
the domain of the Cayley path. -/
theorem Compatible.mem_cayleyDomain_of_continuousLinearEquiv (h₀ : ω.Compatible J₀)
    (h : ω.Tames J) (L : W ≃L[ℝ] F) (hA : A.toLinearMap = J₀.toLinearMap)
    (hB : B.toLinearMap = J.toLinearMap) {b : ℝ} (hb : |b| ≤ 1) :
    (b, A, B) ∈ cayleyDomain (W →L[ℝ] W) := by
  rw [← map_mem_cayleyDomain_iff L.conjContinuousAlgEquiv]
  exact (h₀.transport L.toLinearEquiv).mem_cayleyDomain (h.transport L.toLinearEquiv)
    hb (by ext; simp [← hA]) (by ext; simp [← hB])

/-- Let `W` be a topological vector space isomorphic to a finite-dimensional normed space, `ω` a
symplectic form on `W`, `J₀` an `ω`-compatible and `J` an `ω`-tame complex structure, represented
by continuous endomorphisms `A` and `B`. Then the Cayley path
`cayleyPathFormula (Real.smoothTransition t) A B` represents an `ω`-tame complex structure, which is
`ω`-compatible when `J` is. -/
theorem Compatible.exists_toLinearMap_eq_cayleyPathFormula (h₀ : ω.Compatible J₀)
    (h : ω.Tames J) (L : W ≃L[ℝ] F) (hA : A.toLinearMap = J₀.toLinearMap)
    (hB : B.toLinearMap = J.toLinearMap) (t : ℝ) :
    ∃ K : AlmostComplexStructure W,
      K.toLinearMap = (cayleyPathFormula (Real.smoothTransition t) A B).toLinearMap ∧
        ω.Tames K ∧ (ω.Compatible J → ω.Compatible K) := by
  have h₀' := h₀.transport L.toLinearEquiv
  have h' := h.transport L.toLinearEquiv
  refine ⟨(h₀'.cayleyPath h' t).transport L.toLinearEquiv.symm, ?_, ?_, fun hc ↦ ?_⟩
  · have hL := h₀'.toContinuousLinearMap_cayleyPath h' t
      (A := L.conjContinuousAlgEquiv A) (B := L.conjContinuousAlgEquiv B) (by ext; simp [← hA])
      (by ext; simp [← hB])
    rw [← map_cayleyPathFormula] at hL
    ext v
    have := congrArg (fun C : F →L[ℝ] F ↦ L.symm (C (L v))) hL
    simpa [AlmostComplexStructure.transport_apply] using this
  · simpa [transport_transport_symm] using
      (h₀'.tames_cayleyPath h' t).transport L.toLinearEquiv.symm
  · simpa [transport_transport_symm] using
      (h₀'.compatible_cayleyPath (hc.transport L.toLinearEquiv) t).transport L.toLinearEquiv.symm

end ContinuousLinearEquiv

end TauCeti.SymplecticForm

end
