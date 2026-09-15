import Mathlib
import OPAC016Arithmetic
import OPAC016BalancedProjection

/-!
Sharp balanced-block polytope factor for AXZ-OPAC-016.

The projected long root is the exact factor `2 - 2/b` times a uniform convex
average of A-type roots.  Conversely, every point in the A-root polytope has
each coordinate at most one, giving the matching lower bound from a single
coordinate functional.
-/

namespace OPAC016

open scoped BigOperators

def aRoot {b : ℕ} (i j : Fin b) : Coord b :=
  coordVec i 1 - coordVec j 1

def aRoots (b : ℕ) : Set (Coord b) :=
  {x | ∃ i j, i ≠ j ∧ x = aRoot i j}

def aRootPolytope (b : ℕ) : Set (Coord b) :=
  convexHull ℝ (aRoots b)

def others {b : ℕ} (i : Fin b) : Finset (Fin b) :=
  Finset.univ.erase i

noncomputable def averageARoot {b : ℕ} (i : Fin b) : Coord b :=
  ∑ j ∈ others i, ((1 : ℝ) / (b - 1)) • aRoot i j

@[simp] theorem aRoot_apply_self_left {b : ℕ} {i j : Fin b} (hij : i ≠ j) :
    aRoot i j i = 1 := by
  simp [aRoot, coordVec, hij]

theorem aRoot_coord_le {b : ℕ} (p q i : Fin b) :
    aRoot p q i ≤ (1 : ℝ) := by
  by_cases hip : i = p <;> by_cases hiq : i = q <;>
    simp [aRoot, coordVec, hip, hiq]

theorem aRoot_mem_aRoots {b : ℕ} {i j : Fin b} (hij : i ≠ j) :
    aRoot i j ∈ aRoots b := by
  exact ⟨i, j, hij, rfl⟩

theorem aRootPolytope_coord_le {b : ℕ} {x : Coord b}
    (hx : x ∈ aRootPolytope b) (i : Fin b) : x i ≤ (1 : ℝ) := by
  have hsub : aRoots b ⊆ {y : Coord b | y i ≤ (1 : ℝ)} := by
    intro y hy
    rcases hy with ⟨p, q, hpq, rfl⟩
    exact aRoot_coord_le p q i
  have hlin : IsLinearMap ℝ (fun y : Coord b => y i) :=
    .mk (by intro x y; rfl) (by intro c x; rfl)
  exact (convexHull_min hsub (convex_halfSpace_le hlin 1)) hx

theorem others_card {b : ℕ} (i : Fin b) : (others i).card = b - 1 := by
  simp [others]

theorem averageARoot_mem_polytope {b : ℕ} (hb : 2 ≤ b) (i : Fin b) :
    averageARoot i ∈ aRootPolytope b := by
  let w : Fin b → ℝ := fun _ => (1 : ℝ) / (b - 1)
  let z : Fin b → Coord b := fun j => aRoot i j
  have hb1n : 0 < b - 1 := by omega
  have hb1 : (0 : ℝ) < (b - 1 : ℕ) := by exact_mod_cast hb1n
  have hw0 : ∀ j ∈ others i, 0 ≤ w j := by
    intro j hj
    dsimp [w]
    positivity
  have hw1 : ∑ j ∈ others i, w j = 1 := by
    dsimp [w]
    rw [Finset.sum_const, others_card]
    norm_num [nsmul_eq_mul]
    field_simp
  have hz : ∀ j ∈ others i, z j ∈ aRootPolytope b := by
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    exact subset_convexHull ℝ (aRoots b) (aRoot_mem_aRoots hji.symm)
  have hmem := (convex_convexHull ℝ (aRoots b)).sum_mem hw0 hw1 hz
  simpa [averageARoot, w, z] using hmem

@[simp] theorem projectedLong_apply_self {b : ℕ} (i : Fin b) :
    projectedLong i i = 2 - (2 : ℝ) / b := by
  simp [projectedLong, coordVec]

@[simp] theorem projectedLong_apply_ne {b : ℕ} {i k : Fin b} (hki : k ≠ i) :
    projectedLong i k = -(2 : ℝ) / b := by
  simp [projectedLong, coordVec, hki]

theorem averageARoot_apply_self {b : ℕ} (hb : 2 ≤ b) (i : Fin b) :
    averageARoot i i = 1 := by
  have hb1n : b - 1 ≠ 0 := by omega
  simp [averageARoot, others, aRoot, coordVec, hb1n]

theorem averageARoot_apply_ne {b : ℕ} (hb : 2 ≤ b) {i k : Fin b} (hki : k ≠ i) :
    averageARoot i k = -((1 : ℝ) / (b - 1)) := by
  have hkmem : k ∈ others i := by simp [others, hki]
  have hb1n : b - 1 ≠ 0 := by omega
  simp [averageARoot, others, aRoot, coordVec, hki, hkmem, hb1n]

theorem projectedLong_eq_score_smul_average {b : ℕ} (hb : 2 ≤ b) (i : Fin b) :
    projectedLong i = balancedScore (b : ℝ) • averageARoot i := by
  ext k
  by_cases hki : k = i
  · subst k
    simp [balancedScore]
  · rw [projectedLong_apply_ne hki, Pi.smul_apply, averageARoot_apply_ne hb hki]
    have hb0 : (b : ℝ) ≠ 0 := by positivity
    have hb1 : ((b : ℝ) - 1) ≠ 0 := by positivity
    simp [balancedScore]
    field_simp
    ring

end OPAC016
