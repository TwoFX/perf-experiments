import Lake
open Lake DSL

package «BTree» where
  -- add package configuration options here

lean_lib «BTree» where
  -- add library configuration options here

@[default_target]
lean_exe «btree» where
  root := `Main
