import Lake
open Lake DSL

package erdos1052

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.3.0"

@[default_target]
lean_lib Erdos1052

-- 注释掉可执行文件目标，避免 Windows 路径长度限制 (error 206)
-- lean_exe erdos1052 where
--   root := `Main
