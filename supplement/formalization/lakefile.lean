import Lake
open Lake DSL

package tensorRankBridge where
  version := v!"0.1.0"

require matrixMultiplicationAllFields from git
  "https://github.com/YuvalFilmus/matrix-multiplication-block-identities.git" @
  "8e38460c2c04617692a64a826b09e8995ac8717d" / "vendor/navot"

@[default_target]
lean_lib formalization where
  srcDir := "."
  globs := #[.submodules `formalization]
