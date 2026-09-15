import Lake
open Lake DSL

package "opac016-formal" where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

@[default_target]
lean_lib OPAC016Formal where
  roots := #[
    `OPAC016Arithmetic,
    `OPAC016RootPolytope,
    `OPAC016RootSpanned,
    `OPAC016BalancedProjection,
    `OPAC016BalancedPolytope,
    `OPAC016SignedComponents,
    `OPAC016SignedClass,
    `OPAC016ComponentNormal,
    `OPAC016ComponentOrthogonal,
    `OPAC016ComponentProjection
  ]
