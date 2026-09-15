import OPAC016ExactDilation

/-! The finite maximum is the actual least admissible geometric dilation. -/
namespace OPAC016

noncomputable def coordinateDilationScore {n : ℕ}
    (U : Submodule ℝ (Coord n)) : Option (Fin n) → ℝ := by
  classical
  exact fun a => match a with
    | none => 1
    | some i => if coordVec i 1 ∈ U then 1
        else 2 - 2 / (signedClassSize U (i, true) : ℝ)

noncomputable def exactGeometricDilation {n : ℕ}
    (U : Submodule ℝ (Coord n)) : ℝ :=
  Finset.univ.sup' (by simp) (coordinateDilationScore U)

theorem one_le_exactGeometricDilation {n : ℕ}
    (U : Submodule ℝ (Coord n)) : 1 ≤ exactGeometricDilation U := by
  have h := Finset.le_sup' (coordinateDilationScore U)
    (Finset.mem_univ (none : Option (Fin n)))
  exact h

theorem nonfull_score_le_exactGeometricDilation {n : ℕ}
    {U : Submodule ℝ (Coord n)} (i : Fin n) (hi : coordVec i 1 ∉ U) :
    2 - 2 / (signedClassSize U (i, true) : ℝ) ≤ exactGeometricDilation U := by
  have h := Finset.le_sup' (coordinateDilationScore U) (Finset.mem_univ (some i))
  simpa [coordinateDilationScore, hi, exactGeometricDilation] using h

theorem exactGeometricDilation_admissible {n : ℕ}
    {U : Submodule ℝ (Coord n)} (hU : RootSpanned U) (hne : U ≠ ⊥) :
    AdmissibleDilation U (exactGeometricDilation U) := by
  apply (admissibleDilation_iff_coordinate_scores hU hne _).mpr
  exact ⟨one_le_exactGeometricDilation U,
    fun i hi => nonfull_score_le_exactGeometricDilation i hi⟩

theorem exactGeometricDilation_le_admissible {n : ℕ}
    {U : Submodule ℝ (Coord n)} (hU : RootSpanned U) (hne : U ≠ ⊥)
    {K : ℝ} (hK : AdmissibleDilation U K) : exactGeometricDilation U ≤ K := by
  classical
  obtain ⟨h1, hs⟩ := (admissibleDilation_iff_coordinate_scores hU hne K).mp hK
  apply Finset.sup'_le
  intro a _
  cases a with
  | none => exact h1
  | some i =>
    by_cases hi : coordVec i 1 ∈ U
    · simpa [coordinateDilationScore, hi] using h1
    · simpa [coordinateDilationScore, hi] using hs i hi

theorem exactGeometricDilation_isLeast {n : ℕ}
    {U : Submodule ℝ (Coord n)} (hU : RootSpanned U) (hne : U ≠ ⊥) :
    IsLeast {K : ℝ | AdmissibleDilation U K} (exactGeometricDilation U) :=
  ⟨exactGeometricDilation_admissible hU hne,
    fun _ h => exactGeometricDilation_le_admissible hU hne h⟩

theorem geometricKappa_eq_exact {n : ℕ}
    {U : Submodule ℝ (Coord n)} (hU : RootSpanned U) (hne : U ≠ ⊥) :
    sInf {K : ℝ | AdmissibleDilation U K} = exactGeometricDilation U :=
  (exactGeometricDilation_isLeast hU hne).csInf_eq

theorem exactGeometricDilation_lt_two {n : ℕ} (U : Submodule ℝ (Coord n)) :
    exactGeometricDilation U < 2 := by
  classical
  apply (Finset.sup'_lt_iff (by simp)).mpr
  intro a _
  cases a with
  | none => norm_num [coordinateDilationScore]
  | some i =>
    by_cases hi : coordVec i 1 ∈ U
    · norm_num [coordinateDilationScore, hi]
    · simp only [coordinateDilationScore, hi, ↓reduceIte]
      have hb : (0 : ℝ) < signedClassSize U (i, true) :=
        by exact_mod_cast signedClassSize_pos U (i, true)
      have hd : (0 : ℝ) < 2 / (signedClassSize U (i, true) : ℝ) := div_pos (by norm_num) hb
      linarith

theorem exactGeometricDilation_le_rank_bound {n : ℕ} (hn : 2 ≤ n)
    (U : Submodule ℝ (Coord n)) :
    exactGeometricDilation U ≤ 2 - 2 / (n : ℝ) := by
  classical
  have h1 : (1 : ℝ) ≤ 2 - 2 / (n : ℝ) := by
    have h := balancedScore_ge_one (b := (n : ℝ)) (by exact_mod_cast hn)
    simpa only [balancedScore, mul_one_div] using h
  apply Finset.sup'_le
  intro a _
  cases a with
  | none => exact h1
  | some i =>
    by_cases hi : coordVec i 1 ∈ U
    · simpa [coordinateDilationScore, hi] using h1
    · simp only [coordinateDilationScore, hi, ↓reduceIte]
      have hb : (0 : ℝ) < signedClassSize U (i, true) :=
        by exact_mod_cast signedClassSize_pos U (i, true)
      have hbn : (signedClassSize U (i, true) : ℝ) ≤ n := by
        exact_mod_cast signedClassSize_le_rank (nonfull_anchor_balanced U i hi)
      have hd := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 2 by norm_num) hb hbn
      linarith

end OPAC016
