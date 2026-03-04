/-
# Proof Golf — Measuring Proof Complexity

Custom `#golf` command that wraps `example` or `theorem` declarations and reports:
1. **Source score**: non-whitespace characters in the proof body
2. **Term score**: Expr node count of the elaborated proof term (named decls only)
-/

import Lean

open Lean Elab Command Term Meta

/-- Count non-whitespace characters in a string -/
def countNonWS (s : String) : Nat :=
  s.toList.filter (!·.isWhitespace) |>.length

/-- Recursively find a syntax node of a given kind -/
partial def Lean.Syntax.findKind (stx : Syntax) (k : SyntaxNodeKind) : Option Syntax :=
  if stx.getKind == k then some stx
  else match stx with
    | .node _ _ args => args.findSome? (·.findKind k)
    | _ => none

/-- Count nodes in an Expr tree -/
partial def Lean.Expr.nodeCount (e : Expr) : Nat :=
  match e with
  | .app f a => 1 + f.nodeCount + a.nodeCount
  | .lam _ t b _ => 1 + t.nodeCount + b.nodeCount
  | .forallE _ t b _ => 1 + t.nodeCount + b.nodeCount
  | .letE _ t v b _ => 1 + t.nodeCount + v.nodeCount + b.nodeCount
  | .mdata _ e => e.nodeCount
  | .proj _ _ e => 1 + e.nodeCount
  | _ => 1  -- bvar, fvar, mvar, sort, const, lit

/-- Try to extract a declaration name from a command syntax -/
def getDeclName? (cmd : Syntax) : Option Name :=
  if let some declId := cmd.findKind ``Lean.Parser.Command.declId then
    if declId.getNumArgs > 0 then
      let nameStx := declId.getArg 0
      if nameStx.isIdent then some nameStx.getId else none
    else none
  else none

/-- `#golf` wraps a declaration and reports proof complexity.

- Source score: non-whitespace characters in the proof (after `:= by` or `:=`)
- Term score: Expr nodes in the elaborated proof term (requires `theorem`, not `example`)

```
#golf example (P : Prop) : P → P := by exact id
-- Golf: 7 chars

#golf theorem myThm (P : Prop) : P → P := by exact id
-- Golf: 7 chars | term: 5 nodes
```
-/
elab "#golf " cmd:command : command => do
  elabCommand cmd
  -- Source-level measurement
  let some valStx := cmd.raw.findKind ``Lean.Parser.Command.declValSimple
    | logInfo "Could not find proof body"; return
  let proofStx :=
    match valStx.findKind ``Lean.Parser.Tactic.tacticSeq with
    | some tseq => tseq
    | none => if valStx.getNumArgs > 1 then valStx.getArg 1 else valStx
  let fileMap ← getFileMap
  let some startPos := proofStx.getPos?
    | logInfo "Could not get start position"; return
  let some endPos := proofStx.getTailPos?
    | logInfo "Could not get end position"; return
  let src := (Substring.Raw.mk fileMap.source startPos endPos).toString
  let charScore := countNonWS src
  -- Term-level measurement (only for named declarations)
  let termInfo ←
    if let some declName := getDeclName? cmd.raw then
      let env ← getEnv
      if let some ci := env.find? declName then
        if let some val := ci.value? then
          pure s!" | term: {val.nodeCount} nodes"
        else pure ""
      else pure ""
    else pure ""
  logInfo m!"Golf: {charScore} chars{termInfo}"

