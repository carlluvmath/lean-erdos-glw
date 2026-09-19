import Lake
open Lake DSL

package erdos_glw

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
  @ "dec5b2b780537b6eaf7f5e5f000c12f7387fb24d"

@[default_target]
lean_lib ErdosGLW
