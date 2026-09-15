import OPAC016LeastDilation

/-! The largest balanced signed component gives the closed-form dilation. -/
namespace OPAC016

theorem exactGeometricDilation_le_component_bound {n b : ℕ}
    (U : Submodule ℝ (Coord n)) (hb : 2 ≤ b)
    (hall : ∀ i, coordVec i 1 ∉ U → signedClassSize U (i, true) ≤ b) :
    exactGeometricDilation U ≤ 2 - 2 / (b : ℝ) := by
  classical
  have h1 : (1 : ℝ) ≤ 2 - 2 / (b : ℝ) := by
    have h := balancedScore_ge_one (b := (b : ℝ)) (by exact_mod_cast hb)
    simpa only [balancedScore, mul_one_div] using h
  apply Finset.sup'_le
  intro a _
  cases a with
  | none => exact h1
  | some i =>
    by_cases hi : coordVec i 1 ∈ U
    · simpa [coordinateDilationScore, hi] using h1
    · simp only [coordinateDilationScore, hi, ↓reduceIte]
      have hp : (0 : ℝ) < signedClassSize U (i, true) :=
        by exact_mod_cast signedClassSize_pos U (i, true)
      have hle : (signedClassSize U (i, true) : ℝ) ≤ b := by
        exact_mod_cast hall i hi
      have hd := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 2 by norm_num) hp hle
      linarith

theorem exactGeometricDilation_eq_balanced_max {n b : ℕ}
    (U : Submodule ℝ (Coord n)) (hb : 2 ≤ b)
    (hall : ∀ i, coordVec i 1 ∉ U → signedClassSize U (i, true) ≤ b)
    (hattain : ∃ i, coordVec i 1 ∉ U ∧ signedClassSize U (i, true) = b) :
    exactGeometricDilation U = 2 - 2 / (b : ℝ) := by
  apply le_antisymm (exactGeometricDilation_le_component_bound U hb hall)
  obtain ⟨i, hi, heq⟩ := hattain
  simpa [heq] using nonfull_score_le_exactGeometricDilation i hi

theorem exactGeometricDilation_eq_one_of_no_balanced_block {n : ℕ}
    (U : Submodule ℝ (Coord n))
    (h : ∀ i, coordVec i 1 ∉ U → signedClassSize U (i, true) ≤ 1) :
    exactGeometricDilation U = 1 := by
  apply le_antisymm _ (one_le_exactGeometricDilation U)
  have hb := exactGeometricDilation_le_component_bound U (by decide : 2 ≤ 2)
    (fun i hi => le_trans (h i hi) (by decide : 1 ≤ 2))
  norm_num at hb
  exact hb

end OPAC016
