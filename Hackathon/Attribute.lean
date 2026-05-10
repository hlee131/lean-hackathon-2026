prelude
import Lean.Elab.InfoTree.Main
import Lean

namespace Lean
namespace Environment

open Lean Meta

set_option maxRecDepth 100
-- set_option trace.compiler.ir.init true

def getAttrArgs (stx : Syntax) : List Name :=
  -- stx[0] is the name `unshared`
  -- stx[1] contains the list of arguments
  let argNodes := stx[1].getArgs
  argNodes.toList.filterMap fun arg =>
    if arg.isIdent then some arg.getId else none

def wrapNameWithTrace (e : Expr) (targetName : Name) : MetaM Expr := do
  match e with
  | .lam .. =>
      -- 1. If it's a function, "open" it to get actual variables (xs)
      lambdaTelescope e fun xs body => do
        -- 2. Now 'body' contains FVars instead of BVars.
        -- Run the transform on this 'opened' body.
        let transformedBody ← Meta.transform body (pre := fun sub => do
          match sub with
          | .fvar fvarId =>
              let decl ← fvarId.getDecl

              if decl.userName == targetName then
                IO.println s!"Injecting at {sub}"
                let traceExpr ← mkAppM ``dbgTraceIfShared #[mkStrLit targetName.toString, sub]
                return .done traceExpr
              else
                return .continue
          | _ => return .continue)

        -- 3. Close the telescope to turn FVars back into BVars
        mkLambdaFVars xs transformedBody

  | _ =>
      -- If it's not a lambda, just run the transform normally
      Meta.transform e (pre := fun sub => do
        if sub.isConstOf targetName then
          IO.println s!"Injecting at {sub}"
          let traceExpr ← mkAppM ``dbgTraceIfShared #[mkStrLit targetName.toString, sub]
          return .done traceExpr
        return .continue)

initialize registerBuiltinAttribute {
  name := `unshared
  descr := "Specify unshared references"
  add := fun decl stx kind => do
    let targetNames := getAttrArgs stx

    if targetNames.isEmpty then
      throwError "Attribute [unshared] requires at least one argument (e.g., [unshared arr])"

    let info ← getConstInfo decl
    match info with
    | .defnInfo w =>
      -- 2. Run the instrumentation for each target name
      IO.println s!"Original Body: {w.value}"
      let mut currentBody := w.value
      for target in targetNames do
        currentBody ← MetaM.run' (wrapNameWithTrace currentBody target)

      -- 3. Proceed with addAndCompile/implementedBy using the fully transformed body
      let implName := decl ++ `_unshared_impl
      let implDecl := Declaration.defnDecl { w with name := implName, value := currentBody }
      addAndCompile implDecl
      setImplementedBy decl implName

      -- IO.println s!"{decl} is implemented by {implName}"
      IO.println s!"Implementation of {implName}: {currentBody}"

    | _ => throwError "Attribute @[unshared] only works on definitions."
  applicationTime := AttributeApplicationTime.afterTypeChecking
}
