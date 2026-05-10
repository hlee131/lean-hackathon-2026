import Lean

register_option unshared.runtimeWarning : Bool := {
    defValue := false
    descr := "Set to true to inject dbgTraceIfShared runtime warnings for let +unshared declarations"
}
