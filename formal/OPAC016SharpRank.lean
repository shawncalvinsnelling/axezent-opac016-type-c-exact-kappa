import OPAC016LeastDilation

/-! Sharpness of the rank bound, including the rank-one boundary. -/
namespace OPAC016
open scoped BigOperators

theorem coordVec_not_mem_zeroSum {n : ℕ} (i : Fin n) :
    coordVec i 1 ∉ zeroSumSubspace n := by
  rw [mem_zeroSumSubspace_iff, sum_coordVec]
  norm_num

theorem coordDifference_mem_induced_zeroSum {n : ℕ} (i j : Fin n) (h : i ≠ j) :
    coordVec i 1 - coordVec j 1 ∈ inducedRoots (zeroSumSubspace n) := by
  refine ⟨Or.inr ⟨i, j, true, false, h, ?_⟩, ?_⟩
  · ext k
    by_cases hk : k = j <;> simp [shortRoot, coordVec, rootSign, hk, sub_eq_add_neg]
  · change coordVec i 1 - coordVec j 1 ∈ zeroSumSubspace n
    rw [mem_zeroSumSubspace_iff]
    change (∑ k, (coordVec i 1 k - coordVec j 1 k)) = 0
    rw [Finset.sum_sub_distrib, sum_coordVec, sum_coordVec, sub_self]

theorem zeroSum_rootSpanned {n : ℕ} (hn : 0 < n) :
    RootSpanned (zeroSumSubspace n) := by
  apply le_antisymm (span_inducedRoots_le _)
  intro v hv
  let j : Fin n := ⟨0, hn⟩
  have hvsum : ∑ i, v i = 0 := (mem_zeroSumSubspace_iff v).mp hv
  have heq : (∑ i, v i • (coordVec i 1 - coordVec j 1)) = v := by
    ext k
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
      mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hvsum]
    simp [coordVec]
  rw [← heq]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  by_cases hij : i = j
  · subst i
    simp
  · exact Submodule.subset_span (coordDifference_mem_induced_zeroSum i j hij)

theorem zeroSum_ne_bot {n : ℕ} (hn : 2 ≤ n) : zeroSumSubspace n ≠ ⊥ := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  have h := (coordDifference_mem_induced_zeroSum i j hij).2
  intro hz
  change coordVec i 1 - coordVec j 1 ∈ zeroSumSubspace n at h
  rw [hz, Submodule.mem_bot] at h
  have hc := congrArg (fun v : Coord n => v i) h
  simpa [coordVec, hij] using hc

theorem zeroSum_exactGeometricDilation {n : ℕ} (hn : 2 ≤ n) :
    exactGeometricDilation (zeroSumSubspace n) = 2 - 2 / (n : ℝ) := by
  apply le_antisymm (exactGeometricDilation_le_rank_bound hn _)
  let i : Fin n := ⟨0, by omega⟩
  have ha := exactGeometricDilation_admissible
    (zeroSum_rootSpanned (by omega : 0 < n)) (zeroSum_ne_bot hn)
  have hx : coordVec i 2 ∈ typeCRootPolytope n :=
    subset_convexHull ℝ _ (Or.inl ⟨i, true, by simp [longRoot, rootSign]⟩)
  obtain ⟨y, hy, heq⟩ := ha.2 _ hx
  have hc := congrArg (fun v : Coord n => v i) heq
  rw [starProjection_longRoot_zeroSum] at hc
  have hb := inducedPolytope_coord_le_nonfull (coordVec_not_mem_zeroSum i) hy
  simp only [PiLp.smul_apply, smul_eq_mul] at hc
  have hp : projectedLong i i = 2 - 2 / (n : ℝ) := by simp [projectedLong]
  rw [hp] at hc
  nlinarith [ha.1]

theorem rank_one_exactGeometricDilation (U : Submodule ℝ (Coord 1)) :
    exactGeometricDilation U = 1 := by
  apply le_antisymm _ (one_le_exactGeometricDilation U)
  classical
  apply Finset.sup'_le
  intro a _
  cases a with
  | none => rfl
  | some i =>
    by_cases hi : coordVec i 1 ∈ U
    · simp [coordinateDilationScore, hi]
    · have hlo := signedClassSize_pos U (i, true)
      have hhi := signedClassSize_le_rank (nonfull_anchor_balanced U i hi)
      have heq : signedClassSize U (i, true) = 1 := by omega
      norm_num [coordinateDilationScore, hi, heq]

theorem rank_bound_isGreatest {n : ℕ} (hn : 2 ≤ n) :
    IsGreatest {K : ℝ | ∃ U : Submodule ℝ (Coord n),
      RootSpanned U ∧ U ≠ ⊥ ∧ K = exactGeometricDilation U}
      (2 - 2 / (n : ℝ)) := by
  refine ⟨⟨zeroSumSubspace n, zeroSum_rootSpanned (by omega),
    zeroSum_ne_bot hn, (zeroSum_exactGeometricDilation hn).symm⟩, ?_⟩
  rintro K ⟨U, _, _, rfl⟩
  exact exactGeometricDilation_le_rank_bound hn U

theorem top_rootSpanned (n : ℕ) : RootSpanned (⊤ : Submodule ℝ (Coord n)) := by
  apply le_antisymm le_top
  intro v _
  have heq : (∑ i, (v i / 2) • longRoot i true) = v := by
    ext k
    simp [WithLp.ofLp_sum, longRoot, coordVec, rootSign, Pi.single_apply,
      mul_ite, Finset.sum_ite_eq']
  rw [← heq]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨Or.inl ⟨i, true, rfl⟩, Submodule.mem_top⟩

theorem rank_one_isGreatest :
    IsGreatest {K : ℝ | ∃ U : Submodule ℝ (Coord 1),
      RootSpanned U ∧ U ≠ ⊥ ∧ K = exactGeometricDilation U} 1 := by
  have hn : (⊤ : Submodule ℝ (Coord 1)) ≠ ⊥ := by
    intro heq
    have h : coordVec (0 : Fin 1) 1 ∈ (⊤ : Submodule ℝ (Coord 1)) := Submodule.mem_top
    rw [heq, Submodule.mem_bot] at h
    have hc := congrArg (fun v : Coord 1 => v 0) h
    simpa using hc
  refine ⟨⟨⊤, top_rootSpanned 1, hn, (rank_one_exactGeometricDilation ⊤).symm⟩, ?_⟩
  rintro K ⟨U, _, _, rfl⟩
  exact le_of_eq (rank_one_exactGeometricDilation U)

end OPAC016
