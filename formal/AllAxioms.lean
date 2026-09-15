import OPAC016Arithmetic
import OPAC016BalancedMaximum
import OPAC016BalancedPolytope
import OPAC016BalancedProjection
import OPAC016ComponentNormal
import OPAC016ComponentOrthogonal
import OPAC016CoordinateProjection
import OPAC016DilationLowerBound
import OPAC016ExactDilation
import OPAC016Imports
import OPAC016LeastDilation
import OPAC016RootCertificate
import OPAC016RootPolytope
import OPAC016RootSpanned
import OPAC016SharpRank
import OPAC016SignedClass
import OPAC016SignedComponents
#print axioms OPAC016.balancedScore_ge_one
#print axioms OPAC016.full_balanced_le
#print axioms OPAC016.two_balanced_le
#print axioms OPAC016.compatible_same_block_le
#print axioms OPAC016.incompatible_same_block_le
#print axioms OPAC016.balanced_inactive_le
#print axioms OPAC016.full_inactive_le
#print axioms OPAC016.global_bound
#print axioms OPAC016.exactGeometricDilation_le_component_bound
#print axioms OPAC016.exactGeometricDilation_eq_balanced_max
#print axioms OPAC016.exactGeometricDilation_eq_one_of_no_balanced_block
#print axioms OPAC016.coordLinear_apply
#print axioms OPAC016.aRoot_apply_self_left
#print axioms OPAC016.aRoot_coord_le
#print axioms OPAC016.aRoot_mem_aRoots
#print axioms OPAC016.aRootPolytope_coord_le
#print axioms OPAC016.others_card
#print axioms OPAC016.cast_b_sub_one
#print axioms OPAC016.averageARoot_mem_polytope
#print axioms OPAC016.projectedLong_apply_self
#print axioms OPAC016.projectedLong_apply_ne
#print axioms OPAC016.averageARoot_apply_self
#print axioms OPAC016.averageARoot_apply_ne
#print axioms OPAC016.projectedLong_eq_score_smul_average
#print axioms OPAC016.ones_apply
#print axioms OPAC016.inner_ones_eq_sum
#print axioms OPAC016.mem_zeroSumSubspace_iff
#print axioms OPAC016.sum_coordVec
#print axioms OPAC016.sum_ones
#print axioms OPAC016.projectedLong_mem_zeroSum
#print axioms OPAC016.discardedPart_mem_orthogonal
#print axioms OPAC016.longRoot_decomposition
#print axioms OPAC016.starProjection_longRoot_zeroSum
#print axioms OPAC016.signedCoordVec_apply_self
#print axioms OPAC016.signedCoordVec_apply_ne
#print axioms OPAC016.signedCoordVec_flip
#print axioms OPAC016.shortRoot_eq_signedCoordVec_sub
#print axioms OPAC016.inner_signedCoordVec
#print axioms OPAC016.inner_signedCoordVec_self
#print axioms OPAC016.inner_componentNormal_eq_sum
#print axioms OPAC016.inner_componentNormal_of_mem_orthogonal
#print axioms OPAC016.inner_componentNormal_signedCoordVec
#print axioms OPAC016.inner_componentNormal_signedCoordVec_eq_of_connected
#print axioms OPAC016.componentNormal_inner_inducedRoot_zero
#print axioms OPAC016.componentNormal_mem_orthogonal_of_rootSpanned
#print axioms OPAC016.componentProjectedCoord_mem
#print axioms OPAC016.starProjection_coord_nonfull
#print axioms OPAC016.starProjection_coord_full
#print axioms OPAC016.starProjection_long_nonfull
#print axioms OPAC016.componentNormal_apply_anchor
#print axioms OPAC016.projected_long_anchor_coordinate
#print axioms OPAC016.inducedRoot_coord_le_nonfull
#print axioms OPAC016.inducedPolytope_coord_le_nonfull
#print axioms OPAC016.nonfull_dilation_lower_bound
#print axioms OPAC016.inducedRoots_neg
#print axioms OPAC016.inducedPolytope_neg
#print axioms OPAC016.zero_mem_inducedPolytope
#print axioms OPAC016.convex_dilatedInduced
#print axioms OPAC016.dilatedInduced_neg
#print axioms OPAC016.smul_mem_dilatedInduced
#print axioms OPAC016.projected_coord_singleton
#print axioms OPAC016.coordinate_upper_certificate
#print axioms OPAC016.admissibleDilation_iff_coordinate_scores
#print axioms OPAC016.one_le_exactGeometricDilation
#print axioms OPAC016.nonfull_score_le_exactGeometricDilation
#print axioms OPAC016.exactGeometricDilation_admissible
#print axioms OPAC016.exactGeometricDilation_le_admissible
#print axioms OPAC016.exactGeometricDilation_isLeast
#print axioms OPAC016.geometricKappa_eq_exact
#print axioms OPAC016.exactGeometricDilation_lt_two
#print axioms OPAC016.exactGeometricDilation_le_rank_bound
#print axioms OPAC016.classDifference_anchor
#print axioms OPAC016.classOthers_card
#print axioms OPAC016.classDifference_mem_induced
#print axioms OPAC016.sum_classDifference
#print axioms OPAC016.componentRootAverage_mem
#print axioms OPAC016.projected_long_eq_score_average
#print axioms OPAC016.coordVec_apply_self
#print axioms OPAC016.coordVec_apply_ne
#print axioms OPAC016.rootSign_sq
#print axioms OPAC016.longRoot_mem_longRoots
#print axioms OPAC016.shortRoot_eq_midpoint
#print axioms OPAC016.shortRoot_mem_longRootPolytope
#print axioms OPAC016.typeCRoots_subset_longRootPolytope
#print axioms OPAC016.longRoots_subset_typeCRoots
#print axioms OPAC016.typeCRootPolytope_eq_longRootPolytope
#print axioms OPAC016.inducedRoots_subset_subspace
#print axioms OPAC016.inducedRoots_subset_typeCRoots
#print axioms OPAC016.rootSpanned_iff_span_inter
#print axioms OPAC016.span_inducedRoots_le
#print axioms OPAC016.rootSpanned_nonzero_has_root
#print axioms OPAC016.coordVec_not_mem_zeroSum
#print axioms OPAC016.coordDifference_mem_induced_zeroSum
#print axioms OPAC016.zeroSum_rootSpanned
#print axioms OPAC016.zeroSum_ne_bot
#print axioms OPAC016.zeroSum_exactGeometricDilation
#print axioms OPAC016.rank_one_exactGeometricDilation
#print axioms OPAC016.rank_bound_isGreatest
#print axioms OPAC016.top_rootSpanned
#print axioms OPAC016.rank_one_isGreatest
#print axioms OPAC016.mem_signedClassFinset
#print axioms OPAC016.anchor_mem_signedClassFinset
#print axioms OPAC016.signedClassSize_pos
#print axioms OPAC016.signedBalancedAt_no_opposite
#print axioms OPAC016.bool_eq_or_eq_not
#print axioms OPAC016.signedClass_fst_injOn
#print axioms OPAC016.signedClassSize_le_rank
#print axioms OPAC016.nonfull_anchor_balanced
#print axioms OPAC016.coord_zero_of_coordVec_one_mem
#print axioms OPAC016.connected_anchor_true_to_full
#print axioms OPAC016.rootSign_not
#print axioms OPAC016.inner_longRoot
#print axioms OPAC016.inner_shortRoot
#print axioms OPAC016.signedEdge_value_eq
#print axioms OPAC016.signedConnected_value_eq
#print axioms OPAC016.signedConnected_shortRoot_mem
#print axioms OPAC016.signedEdge_complement
#print axioms OPAC016.signedConnected_complement
#print axioms OPAC016.signed_unbalanced_coord_zero
#print axioms OPAC016.longRoot_coord_zero
#print axioms OPAC016.coordVec_mem_of_orthogonal_coord_zero
#print axioms OPAC016.longRoot_forces_coordinate_line
#print axioms OPAC016.unbalanced_forces_coordinate_line
