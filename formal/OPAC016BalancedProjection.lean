import Mathlib
import OPAC016RootPolytope

/-!
Balanced Type-A block geometry inside the Type-C proof.

A balanced block on `b` coordinates is the zero-sum hyperplane.  We realize it
as the orthogonal complement of the all-ones line and prove the exact
orthogonal projection of a Type-C long root onto that hyperplane.
-/

namespace OPAC016

open scoped BigOperators

def ones (b : ℕ) : Coord b :=
  WithLp.toLp 2 (fun _ : Fin b => (1 : ℝ))

@[simp] theorem ones_apply {b : ℕ} (i : Fin b) : ones b i = 1 := by
  rfl

noncomputable def zeroSumSubspace (b : ℕ) : Submodule ℝ (Coord b) :=
  (ℝ ∙ ones b)ᗮ

theorem inner_ones_eq_sum {b : ℕ} (v : Coord b) :
    @inner ℝ (Coord b) _ (ones b) v = ∑ j, v j := by
  rw [PiLp.inner_apply]
  simp [ones, RCLike.inner_apply]

theorem mem_zeroSumSubspace_iff {b : ℕ} (v : Coord b) :
    v ∈ zeroSumSubspace b ↔ ∑ j, v j = 0 := by
  rw [zeroSumSubspace, Submodule.mem_orthogonal_singleton_iff_inner_right,
    inner_ones_eq_sum]

theorem sum_coordVec {b : ℕ} (i : Fin b) (a : ℝ) :
    (∑ j, coordVec i a j) = a := by
  simp [coordVec]

theorem sum_ones (b : ℕ) :
    (∑ j : Fin b, ones b j) = b := by
  simp [ones]

noncomputable def projectedLong {b : ℕ} (i : Fin b) : Coord b :=
  coordVec i 2 - ((2 : ℝ) / b) • ones b

theorem projectedLong_mem_zeroSum {b : ℕ} (i : Fin b) :
    projectedLong i ∈ zeroSumSubspace b := by
  rw [mem_zeroSumSubspace_iff]
  have hi : i.val < b := i.isLt
  have hbn : b ≠ 0 := by omega
  have hb : (b : ℝ) ≠ 0 := by exact_mod_cast hbn
  change Finset.univ.sum
      (fun j : Fin b => (coordVec i 2) j - ((2 : ℝ) / b) * (ones b) j) = 0
  rw [Finset.sum_sub_distrib, sum_coordVec]
  simp only [ones_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hb]

theorem discardedPart_mem_orthogonal {b : ℕ} (_i : Fin b) :
    ((2 : ℝ) / b) • ones b ∈ (zeroSumSubspace b)ᗮ := by
  apply Submodule.le_orthogonal_orthogonal
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self (ones b))

theorem longRoot_decomposition {b : ℕ} (i : Fin b) :
    coordVec i 2 = projectedLong i + ((2 : ℝ) / b) • ones b := by
  simp [projectedLong]

theorem starProjection_longRoot_zeroSum {b : ℕ} (i : Fin b) :
    (zeroSumSubspace b).starProjection (coordVec i 2) = projectedLong i := by
  exact Submodule.eq_starProjection_of_mem_orthogonal'
    (projectedLong_mem_zeroSum i)
    (discardedPart_mem_orthogonal i)
    (longRoot_decomposition i)

end OPAC016
