/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Elab.Syntax

open Lean Elab Command Parser

namespace LeanPy

/-- Create an info tree node recording the elaboration of `stx` by `elaborator`. -/
@[inline] def mkElabInfoTreeCore (elaborator : Name) (stx : Syntax) (trees : PersistentArray InfoTree) : InfoTree :=
  .node (.ofCommandInfo { elaborator, stx }) trees

/-- Create context info for the info tree from the current state of command elaboration.  -/
@[inline] def mkCommandContextInfo
  [Monad m] [MonadEnv m] [MonadOptions m]
  [MonadFileMap m] [MonadResolveName m] [MonadNameGenerator m]
: m CommandContextInfo := do
  return  {
    env := ← getEnv
    fileMap := ← getFileMap
    mctx := {}
    currNamespace := ← getCurrNamespace
    openDecls := ← getOpenDecls
    options := ← getOptions
    ngen := ← getNGen
  }

/-- Create an info tree for an elaborator with the current core elaboration context. -/
@[inline] def mkCommandElabInfoTree
  [Monad m] [MonadEnv m] [MonadOptions m]
  [MonadFileMap m] [MonadResolveName m] [MonadNameGenerator m]
  (elaborator : Name) (stx : Syntax) (trees : PersistentArray InfoTree)
: m InfoTree := do
  return .context (.commandCtx (← mkCommandContextInfo))
    (mkElabInfoTreeCore elaborator stx trees)

instance : MonadMacroAdapter CoreM where
  getCurrMacroScope := return (← read).currMacroScope
  getNextMacroScope := return (← get).nextMacroScope
  setNextMacroScope s := do modify ({· with nextMacroScope := s})

instance [MonadRecDepth m] [MonadLiftT m n] [MonadFunctor m n] : MonadRecDepth n where
  withRecDepth d x := monadMap (m := m) (fun x => MonadRecDepth.withRecDepth d x) x
  getRecDepth      := liftM (m := m) <| MonadRecDepth.getRecDepth
  getMaxRecDepth   := liftM (m := m) <| MonadRecDepth.getMaxRecDepth

local instance [MonadLiftT IO m] : Nonempty (m α) :=
  ⟨liftM (m := IO) <| throw default⟩

/-- Use `f` to handle elaboration on the macro expanded syntax. -/
@[specialize] partial def elabSyntaxWith
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m] [MonadLiftT CoreM m]
  [MonadFinally m] [MonadAlwaysExcept ε m]
  [MonadEnv m] [MonadOptions m] [MonadFileMap m]
  [MonadInfoTree m] [MonadQuotation m] [MonadMacroAdapter m]
  [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m]
  [MonadNameGenerator m] [AddMessageContext m]
  (stx : Syntax) (f : Syntax → m α)
: m α :=
  go stx
where
  go stx :=
    withRef stx <| withIncRecDepth <| withFreshMacroScope do
      withTraceNode `Elab.step (fun _ => return stx) do
        checkSystem "elaborator"
        if let some (decl, stxNew?) ← liftMacroM <| expandMacroImpl? (← getEnv) stx then
          withInfoTreeContext (mkInfoTree := mkCommandElabInfoTree decl stx) do
            let stxNew ← liftMacroM <| liftExcept stxNew?
            withInfoContext (mkInfo := pure <| .ofMacroExpansionInfo { stx := stx, output := stxNew, lctx := .empty }) do
              go stxNew
        else
          f stx


/-- Adapted from the private `elabCommandUsing` definition in `Lean.Elab.Command`. -/
@[specialize] def elabSyntaxUsing?
  [Monad m] [MonadEnv m] [MonadOptions m]
  [MonadFileMap m] [MonadResolveName m] [MonadNameGenerator m]
  [MonadExcept Exception m] [MonadFinally m] [MonadBacktrack σ m] [MonadInfoTree m]
  (stx : Syntax) (elabFns : List (KeyedDeclsAttribute.AttributeEntry (Syntax → m α)))
: m (Option α) := do
  let elabFn::elabFns := elabFns
    | return none
  let s ← saveState
  catchInternalId unsupportedSyntaxExceptionId
    (withInfoTreeContext (mkInfoTree := mkCommandElabInfoTree elabFn.declName stx) do
      elabFn.value stx)
    (fun _ => do restoreState s; elabSyntaxUsing? stx elabFns)

instance : MonadBacktrack Core.State CoreM where
  saveState := get
  restoreState := set

instance (priority := low) [MonadLift m n] [MonadBacktrack σ m] : MonadBacktrack σ n where
  saveState := liftM (m := m) saveState
  restoreState s := liftM (m := m) (restoreState s)
