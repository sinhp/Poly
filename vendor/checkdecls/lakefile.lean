import Lake
open Lake DSL

package «checkdecls» {
  -- add package configuration options here
}

@[default_target]
lean_exe «checkdecls» {
  root := `Main
  supportInterpreter := true
  weakLinkArgs := #["-lLake"]
}
