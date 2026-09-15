import OPAC016Imports
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
  ∑ j ∈ others i, ((1 : ℝ) / ((b : ℝ) - 1)) • aRoot i j

noncomputable def coordLinear {b : ℕ} (i : Fin b) : Coord b →ₗ[ℝ] ℝ where
  toFun x := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coordLinear_apply {b : ℕ} (i : Fin b) (x : Coord b) :
    coordLinear i x = x i := rfl

@[simp] theorem aRoot_apply_self_left {b : ℕ} {i j : Fin b} (hij : i ≠ j) :
    aRoot i j i = 1 := by
  simp [aRoot, coordVec, hij]

theorem aRoot_coord_le {b : ℕ} (p q i : Fin b) :
    aRoot p q i ≤ (1 : ℝ) := by
  by_cases hip : i = p
  · subst i
    by_cases hpq : p = q
    · subst q
      simp [aRoot, coordVec]
    · simp [aRoot, coordVec, hpq]
  · by_cases hiq : i = q
    · subst i
      have hqp : q ≠ p := by simpa [eq_comm] using hip
      simp [aRoot, coordVec, hqp]
    · simp [aRoot, coordVec, hip, hiq]

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

theorem cast_b_sub_one {b : ℕ} (hb : 1 ≤ b) :
    ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
  rw [Nat.cast_sub hb]
  norm_num

theorem averageARoot_mem_polytope {b : ℕ} (hb : 2 ≤ b) (i : Fin b) :
    averageARoot i ∈ aRootPolytope b := by
  let w : Fin b → ℝ := fun _ => (1 : ℝ) / ((b : ℝ) - 1)
  let z : Fin b → Coord b := fun j => aRoot i j
  have hd : 0 < (b : ℝ) - 1 := by
    have hbR : (1 : ℝ) < b := by exact_mod_cast hb
    linarith
  have hw0 : ∀ j ∈ others i, 0 ≤ w j := by
    intro j hj
    dsimp [w]
    positivity
  have hw1 : ∑ j ∈ others i, w j = 1 := by
    dsimp [w]
    rw [Finset.sum_const, others_card, nsmul_eq_mul, cast_b_sub_one (by omega : 1 ≤ b)]
    field_simp [ne_of_gt hd]
  have hz : ∀ j ∈ others i, z j ∈ aRootPolytope b := by
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    exact subset_convexHull ℝ (aRoots b) (aRoot_mem_aRoots hji.symm)
  have hmem := (convex_convexHull ℝ (aRoots b)).sum_mem hw0 hw1 hz
  simpa [averageARoot, w, z, aRootPolytope] using hmem

@[simp] theorem projectedLong_apply_self {b : ℕ} (i : Fin b) :
    projectedLong i i = 2 - (2 : ℝ) / b := by
  simp [projectedLong, coordVec]

@[simp] theorem projectedLong_apply_ne {b : ℕ} {i k : Fin b} (hki : k ≠ i) :
    projectedLong i k = -(2 : ℝ) / b := by
  simp [projectedLong, coordVec, hki]
  ring

theorem averageARoot_apply_self {b : ℕ} (hb : 2 ≤ b) (i : Fin b) :
    averageARoot i i = 1 := by
  have hd : 0 < (b : ℝ) - 1 := by
    have hbR : (1 : ℝ) < b := by exact_mod_cast hb
    linarith
  change coordLinear i (averageARoot i) = 1
  rw [averageARoot, map_sum]
  simp only [map_smul, coordLinear_apply, smul_eq_mul]
  have hsum :
      (∑ j ∈ others i, ((1 : ℝ) / ((b : ℝ) - 1)) * aRoot i j i) =
      ∑ j ∈ others i, ((1 : ℝ) / ((b : ℝ) - 1)) * 1 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [aRoot_apply_self_left]
    exact (Finset.mem_erase.mp hj).1.symm
  rw [hsum, Finset.sum_const, others_card, nsmul_eq_mul,
    cast_b_sub_one (by omega : 1 ≤ b)]
  field_simp [ne_of_gt hd]

theorem averageARoot_apply_ne {b : ℕ} (_hb : 2 ≤ b) {i k : Fin b} (hki : k ≠ i) :
    averageARoot i k = -((1 : ℝ) / ((b : ℝ) - 1)) := by
  have hkmem : k ∈ others i := by simp [others, hki]
  change coordLinear k (averageARoot i) = -((1 : ℝ) / ((b : ℝ) - 1))
  rw [averageARoot, map_sum]
  simp only [map_smul, coordLinear_apply, smul_eq_mul]
  rw [Finset.sum_eq_single_of_mem k hkmem]
  · simp [aRoot, coordVec, hki]
  · intro j hj hjk
    have hkj : k ≠ j := by exact Ne.symm hjk
    simp [aRoot, coordVec, hki, hkj]

theorem projectedLong_eq_score_smul_average {b : ℕ} (hb : 2 ≤ b) (i : Fin b) :
    projectedLong i = balancedScore (b : ℝ) • averageARoot i := by
  ext k
  by_cases hki : k = i
  · subst k
    simp only [PiLp.smul_apply, projectedLong_apply_self, averageARoot_apply_self hb, smul_eq_mul]
    simp [balancedScore]
    ring
  · simp only [PiLp.smul_apply, projectedLong_apply_ne hki,
      averageARoot_apply_ne hb hki, smul_eq_mul]
    have hb0 : (b : ℝ) ≠ 0 := by
      have : (0 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hb)
      exact ne_of_gt this
    have hb1 : ((b : ℝ) - 1) ≠ 0 := by
      have : (1 : ℝ) < b := by exact_mod_cast hb
      linarith
    simp [balancedScore]
    field_simp [hb0, hb1]

end OPAC016
