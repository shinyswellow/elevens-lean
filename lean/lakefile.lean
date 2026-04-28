import Lake
open Lake DSL

package «Elevens» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Elevens» where

lean_lib «ElevensChallenge» where

lean_lib «ElevensSolution» where
