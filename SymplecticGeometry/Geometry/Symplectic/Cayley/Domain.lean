/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cayley.Smooth
import Mathlib.Analysis.Normed.Ring.Units

/-!
# The domain of the Cayley path

For `A B` in a ring `R` over `ℝ`, Tau Ceti's Cayley path
`TauCeti.cayleyPathFormula b A B = A (1 + b C)(1 - b C)⁻¹`, with
`C = TauCeti.cayleyFormula A B = -(1 + A B)(1 - A B)⁻¹`, involves two inverses. This file names
the set of triples `(b, A, B)` where both `1 - A B` and `1 - b C` are units, and shows that in a
complete normed `ℝ`-algebra it is open and the Cayley path is smooth on it. The pairs `(A, B)`
for which the whole segment `b ∈ [0, 1]` lies in it form an open set too, by compactness of
`[0, 1]`. For a compatible `J₀` and a tame `J`, every `|b| ≤ 1` gives a point of the domain.

## Main definitions and results

* `TauCeti.cayleyDomain R`: the triples where both denominators are units.
* `TauCeti.isOpen_cayleyDomain`, `TauCeti.contDiffOn_cayleyPathFormula`.
* `TauCeti.isOpen_setOf_forall_Icc_mem_cayleyDomain`: the pairs `(A, B)` whose segment over
  `[0, 1]` lies in the domain form an open set.
* `TauCeti.SymplecticForm.Compatible.mem_cayleyDomain`: a compatible and a tame structure,
  with `|b| ≤ 1`, give a point of the domain.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 2.5.13 (the Cayley transform proof of Sévennec).
-/

public section

open Set Topology

namespace TauCeti

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

end Ring

section Normed

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

omit [NormedAlgebra ℝ R] in
/-- The Cayley coordinate is continuous at every pair `(A, B)` with `1 - A B` a unit. -/
private lemma continuousAt_cayleyFormula {b : ℝ} {A B : R} (h : IsUnit (1 - A * B)) :
    ContinuousAt (fun q : ℝ × R × R ↦ cayleyFormula q.2.1 q.2.2) (b, A, B) := by
  have hAB : ContinuousAt (fun q : ℝ × R × R ↦ q.2.1 * q.2.2) (b, A, B) := by fun_prop
  have hinv : ContinuousAt (fun q : ℝ × R × R ↦ Ring.inverse (1 - q.2.1 * q.2.2)) (b, A, B) :=
    (NormedRing.inverse_continuousAt h.unit).comp_of_eq (continuousAt_const.sub hAB) h.unit_spec
  simp only [cayleyFormula_def]
  exact ((continuousAt_const.add hAB).mul hinv).neg

variable (R) in
/-- The domain of the Cayley path is open. -/
theorem isOpen_cayleyDomain : IsOpen (cayleyDomain R) := by
  have hs : IsOpen {q : ℝ × R × R | IsUnit (1 - q.2.1 * q.2.2)} :=
    Units.isOpen.preimage (by fun_prop)
  have hf : ContinuousOn (fun q : ℝ × R × R ↦ 1 - q.1 • cayleyFormula q.2.1 q.2.2)
      {q | IsUnit (1 - q.2.1 * q.2.2)} := by
    rintro ⟨b, A, B⟩ h
    exact (continuousAt_const.sub
      (continuousAt_fst.smul (continuousAt_cayleyFormula h))).continuousWithinAt
  exact hf.isOpen_inter_preimage hs Units.isOpen

/-- The Cayley path is smooth, jointly in the parameter and both endpoints, on its domain. -/
theorem contDiffOn_cayleyPathFormula {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (fun q : ℝ × R × R ↦ cayleyPathFormula q.1 q.2.1 q.2.2) (cayleyDomain R) :=
  fun _ hq ↦ (contDiffAt_cayleyPathFormula hq.1 hq.2).contDiffWithinAt

variable (R) in
/-- The pairs `(A, B)` such that `(b, A, B)` lies in the domain of the Cayley path for every
`b ∈ [0, 1]` form an open set. -/
theorem isOpen_setOf_forall_Icc_mem_cayleyDomain :
    IsOpen {p : R × R | ∀ b ∈ Icc (0 : ℝ) 1, (b, p.1, p.2) ∈ cayleyDomain R} := by
  refine isOpen_iff_mem_nhds.2 fun p hp ↦ ?_
  refine isCompact_Icc.eventually_forall_of_forall_eventually fun b hb ↦ ?_
  have hc : Continuous fun z : (R × R) × ℝ ↦ (z.2, z.1.1, z.1.2) := by fun_prop
  exact hc.continuousAt.preimage_mem_nhds ((isOpen_cayleyDomain R).mem_nhds (hp b hb))

end Normed

namespace SymplecticForm

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

end SymplecticForm

end TauCeti

end
