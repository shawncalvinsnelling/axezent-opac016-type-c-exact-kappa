import Lake
open Lake DSL

package "opac016-formal" where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

@[default_target]
lean_lib OPAC016Formal where
  roots := #[
    `OPAC016Imports,
    `OPAC016Arithmetic,
    `OPAC016RootPolytope,
    `OPAC016RootSpanned,
    `OPAC016BalancedProjection,
    `OPAC016BalancedPolytope,
    `OPAC016SignedComponents,
    `OPAC016SignedClass,
    `OPAC016ComponentNormal,
    `OPAC016ComponentOrthogonal,
    `OPAC016CoordinateProjection,
    `OPAC016DilationLowerBound,
    `OPAC016RootCertificate,
    `OPAC016ExactDilation,
    `OPAC016LeastDilation,
    `OPAC016BalancedMaximum,
    `OPAC016SharpRank
  ]
