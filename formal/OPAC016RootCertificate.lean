import OPAC016DilationLowerBound
import OPAC016BalancedPolytope

namespace OPAC016
open scoped BigOperators

noncomputable def classOthers {n : ℕ} (U : Submodule ℝ (Coord n)) (i : Fin n) :
    Finset (SignedCoord n) := by
  classical
  exact (signedClassFinset U (i, true)).erase (i, true)

noncomputable def classDifference {n : ℕ} (i : Fin n) (a : SignedCoord n) : Coord n :=
  coordVec i 1 - signedCoordVec a

@[simp] theorem classDifference_anchor {n : ℕ} (i : Fin n) :
    classDifference i (i, true) = 0 := by
  simp [classDifference, signedCoordVec, rootSign]

theorem classOthers_card {n : ℕ} (U : Submodule ℝ (Coord n)) (i : Fin n) :
    (classOthers U i).card = signedClassSize U (i, true) - 1 := by
  classical
  simp [classOthers, Finset.card_erase_of_mem (anchor_mem_signedClassFinset U (i, true)),
    signedClassSize]

theorem classDifference_mem_induced {n : ℕ}
    {U : Submodule ℝ (Coord n)} {i : Fin n} (hnfull : coordVec i 1 ∉ U)
    {a : SignedCoord n} (ha : a ∈ classOthers U i) :
    classDifference i a ∈ inducedRoots U := by
  classical
  have ha' := Finset.mem_erase.mp ha
  have hbal := nonfull_anchor_balanced U i hnfull
  have hne : a.1 ≠ i := by
    intro heq
    have heqa : a = (i, true) :=
      signedClass_fst_injOn hbal ha'.2 (anchor_mem_signedClassFinset U (i, true)) heq
    exact ha'.1 heqa
  have hc : signedConnected U (i, true) a := mem_signedClassFinset.mp ha'.2
  have hu := signedConnected_shortRoot_mem hne.symm hc
  have heq : classDifference i a = shortRoot i a.1 true (!a.2) := by
    rw [shortRoot_eq_signedCoordVec_sub i a.1 true (!a.2) hne.symm]
    simp [classDifference, signedCoordVec, rootSign]
  rw [heq]
  exact ⟨Or.inr ⟨i, a.1, true, !a.2, hne.symm, rfl⟩, hu⟩

theorem sum_classDifference {n : ℕ} (U : Submodule ℝ (Coord n)) (i : Fin n) :
    (∑ a ∈ classOthers U i, classDifference i a) =
      (signedClassSize U (i, true) : ℝ) • coordVec i 1 - componentNormal U i := by
  classical
  have h := Finset.sum_erase_add (signedClassFinset U (i, true))
    (fun a => classDifference i a) (anchor_mem_signedClassFinset U (i, true))
  simp only [classDifference_anchor, add_zero] at h
  rw [classOthers, h]
  simp [classDifference, Finset.sum_sub_distrib, componentNormal, signedClassSize]
  ext j
  simp [coordVec]

noncomputable def componentRootAverage {n : ℕ}
    (U : Submodule ℝ (Coord n)) (i : Fin n) : Coord n :=
  ∑ a ∈ classOthers U i,
    ((1 : ℝ) / ((signedClassSize U (i, true) : ℝ) - 1)) • classDifference i a

theorem componentRootAverage_mem {n : ℕ}
    {U : Submodule ℝ (Coord n)} {i : Fin n} (hnfull : coordVec i 1 ∉ U)
    (hb : 2 ≤ signedClassSize U (i, true)) :
    componentRootAverage U i ∈ inducedPolytope U := by
  let w : SignedCoord n → ℝ := fun _ =>
    1 / ((signedClassSize U (i, true) : ℝ) - 1)
  have hbR : (1 : ℝ) < signedClassSize U (i, true) := by exact_mod_cast hb
  have hw0 : ∀ a ∈ classOthers U i, 0 ≤ w a := by
    intro a ha
    dsimp [w]
    positivity
  have hw1 : ∑ a ∈ classOthers U i, w a = 1 := by
    dsimp [w]
    rw [Finset.sum_const, classOthers_card, nsmul_eq_mul,
      cast_b_sub_one (by omega : 1 ≤ signedClassSize U (i, true))]
    simpa only [mul_one_div] using div_self (ne_of_gt (sub_pos.mpr hbR))
  have hx : ∀ a ∈ classOthers U i, classDifference i a ∈ inducedPolytope U := by
    intro a ha
    exact subset_convexHull ℝ (inducedRoots U) (classDifference_mem_induced hnfull ha)
  have h := (convex_convexHull ℝ (inducedRoots U)).sum_mem hw0 hw1 hx
  simpa [componentRootAverage, w, inducedPolytope] using h

theorem projected_long_eq_score_average {n : ℕ}
    {U : Submodule ℝ (Coord n)} (hU : RootSpanned U)
    (i : Fin n) (hnfull : coordVec i 1 ∉ U)
    (hb : 2 ≤ signedClassSize U (i, true)) :
    U.starProjection (coordVec i 2) =
      (2 - 2 / (signedClassSize U (i, true) : ℝ)) • componentRootAverage U i := by
  have hb0 : (signedClassSize U (i, true) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (signedClassSize_pos U (i, true)))
  have hbR : (1 : ℝ) < signedClassSize U (i, true) := by exact_mod_cast hb
  have hcoef :
      (2 - 2 / (signedClassSize U (i, true) : ℝ)) *
        (1 / ((signedClassSize U (i, true) : ℝ) - 1)) =
      2 / (signedClassSize U (i, true) : ℝ) := by
    field_simp [ne_of_gt (sub_pos.mpr hbR)]
  rw [starProjection_coord_nonfull hU i hnfull, componentRootAverage,
    ← Finset.smul_sum, smul_smul, hcoef, sum_classDifference, smul_sub, smul_smul]
  rw [div_mul_cancel₀ _ hb0]
  congr 1
  ext j
  by_cases hji : j = i <;> simp [componentProjectedCoord, coordVec, hji]

end OPAC016
