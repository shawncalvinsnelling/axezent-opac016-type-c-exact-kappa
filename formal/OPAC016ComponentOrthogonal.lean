import Mathlib
import OPAC016ComponentNormal
import OPAC016RootSpanned

/-!
Root-spanned orthogonality of the signed component normal.
-/

namespace OPAC016

open scoped BigOperators

theorem componentNormal_inner_inducedRoot_zero {n : ℕ}
    {U : Submodule ℝ (Coord n)} {i : Fin n}
    (hnfull : coordVec i 1 ∉ U) {α : Coord n}
    (hα : α ∈ inducedRoots U) :
    @inner ℝ (Coord n) _ (componentNormal U i) α = 0 := by
  have hbal : signedBalancedAt U (i, true) :=
    nonfull_anchor_balanced U i hnfull
  rcases hα.1 with hlong | hshort
  · rcases hlong with ⟨j, s, rfl⟩
    have hjfull : coordVec j 1 ∈ U :=
      longRoot_forces_coordinate_line U j s hα.2 1
    rw [inner_componentNormal_eq_sum]
    apply Finset.sum_eq_zero
    intro a ha
    rcases a with ⟨k, t⟩
    have hconn : signedConnected U (i, true) (k, t) :=
      mem_signedClassFinset.mp ha
    have hne : k ≠ j := by
      intro hkj
      subst k
      have hifull : coordVec i 1 ∈ U :=
        connected_anchor_true_to_full U i j t hconn hjfull 1
      exact hnfull hifull
    simp [signedValue, longRoot, coordVec, hne]
  · rcases hshort with ⟨p, q, sp, sq, hpq, rfl⟩
    have hroot : shortRoot p q sp sq ∈ U := hα.2
    have hedge : signedEdge U (p, sp) (q, !sq) := by
      refine ⟨hpq, ?_⟩
      simpa using hroot
    have hconn : signedConnected U (p, sp) (q, !sq) :=
      Relation.EqvGen.rel _ _ hedge
    have heq := inner_componentNormal_signedCoordVec_eq_of_connected hbal hconn
    rw [shortRoot_eq_signedCoordVec_sub p q sp sq hpq, inner_sub_right, heq, sub_self]

theorem componentNormal_mem_orthogonal_of_rootSpanned {n : ℕ}
    {U : Submodule ℝ (Coord n)} {i : Fin n}
    (hU : RootSpanned U) (hnfull : coordVec i 1 ∉ U) :
    componentNormal U i ∈ Uᗮ := by
  rw [Submodule.mem_orthogonal']
  intro u hu
  have huspan : u ∈ Submodule.span ℝ (inducedRoots U) := by
    rw [hU]
    exact hu
  refine Submodule.span_induction (p := fun x _ =>
      @inner ℝ (Coord n) _ (componentNormal U i) x = 0) ?_ ?_ ?_ ?_ huspan
  · intro x hx
    exact componentNormal_inner_inducedRoot_zero hnfull hx
  · simp
  · intro x y hx hy ihx ihy
    simpa [inner_add_right, ihx, ihy]
  · intro c x hx ihx
    simpa [real_inner_smul_right, ihx]

end OPAC016
