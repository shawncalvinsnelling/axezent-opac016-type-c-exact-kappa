import Mathlib

/-!
Arithmetic kernel for AXZ-OPAC-016.

This file formalizes only the scalar inequalities used after the geometric
component theorem has been established. It is NOT a formalization of the
complete root-system theorem.
-/

namespace OPAC016

noncomputable def balancedScore (b : ℝ) : ℝ := 2 - 2 * (1 / b)

theorem balancedScore_ge_one {b : ℝ} (hb : 2 ≤ b) :
    1 ≤ balancedScore b := by
  unfold balancedScore
  have hrecip : 1 / b ≤ (1 / 2 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) hb
  linarith

theorem full_balanced_le {b B : ℝ}
    (hb : 2 ≤ b) (hB : b ≤ B) :
    (3 / 2 : ℝ) - 1 / b ≤ balancedScore B := by
  unfold balancedScore
  have hbpos : 0 < b := by linarith
  have hrecip : 1 / B ≤ 1 / b := by
    exact one_div_le_one_div_of_le hbpos hB
  have hhalf : 1 / B ≤ (1 / 2 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) (le_trans hb hB)
  linarith

theorem two_balanced_le {b c B : ℝ}
    (hb : 2 ≤ b) (hc : 2 ≤ c) (hbB : b ≤ B) (hcB : c ≤ B) :
    2 - 1 / b - 1 / c ≤ balancedScore B := by
  unfold balancedScore
  have hbpos : 0 < b := by linarith
  have hcpos : 0 < c := by linarith
  have h1 : 1 / B ≤ 1 / b := by
    exact one_div_le_one_div_of_le hbpos hbB
  have h2 : 1 / B ≤ 1 / c := by
    exact one_div_le_one_div_of_le hcpos hcB
  linarith

theorem compatible_same_block_le {B : ℝ} (hB : 2 ≤ B) :
    (1 : ℝ) ≤ balancedScore B :=
  balancedScore_ge_one hB

theorem incompatible_same_block_le {b B : ℝ}
    (hb : 2 ≤ b) (hB : b ≤ B) :
    max (0 : ℝ) (2 - 4 / b) ≤ balancedScore B := by
  unfold balancedScore
  have hB2 : 2 ≤ B := le_trans hb hB
  have htarget_nonneg : 0 ≤ 2 - 2 * (1 / B) := by
    have hrecip : 1 / B ≤ (1 / 2 : ℝ) := by
      exact one_div_le_one_div_of_le (by norm_num) hB2
    linarith
  apply max_le htarget_nonneg
  have hbpos : 0 < b := by linarith
  have hrecip : 1 / B ≤ 1 / b := by
    exact one_div_le_one_div_of_le hbpos hB
  have hinvnonneg : 0 ≤ 1 / b := by positivity
  have hfour : 4 / b = 4 * (1 / b) := by ring
  rw [hfour]
  linarith

theorem balanced_inactive_le {b B : ℝ}
    (hb : 2 ≤ b) (hB : b ≤ B) :
    1 - 1 / b ≤ balancedScore B := by
  have hbase := balancedScore_ge_one (le_trans hb hB)
  have hbpos : 0 < b := by linarith
  have hpos : 0 < 1 / b := one_div_pos.mpr hbpos
  linarith

theorem full_inactive_le {B : ℝ} (hB : 2 ≤ B) :
    (1 / 2 : ℝ) ≤ balancedScore B := by
  have hbase := balancedScore_ge_one hB
  linarith

theorem global_bound {b n : ℝ}
    (hb : 2 ≤ b) (hbn : b ≤ n) :
    balancedScore b ≤ balancedScore n := by
  unfold balancedScore
  have hbpos : 0 < b := by linarith
  have hrecip : 1 / n ≤ 1 / b := by
    exact one_div_le_one_div_of_le hbpos hbn
  linarith

end OPAC016
