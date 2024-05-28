/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command
import Lean.Linter.Util
import Batteries.Data.List.Basic
import Mathlib.Tactic.Lemma

/-!
# A linter to replace `refine'` with `refine`
-/

namespace Mathlib.Linter

/--
The linter helps with the conversion `refine'` to `refine`, by printing the positions of
missing `?`.
-/
register_option linter.refine'ToRefine : Bool := {
  defValue := true
  descr := "flag `refine'` that can be converted to `refine`s"
}

namespace refine'ToRefine

open Lean Elab

/-- converts
* `theorem x ...`  to `example ...`,
* `lemma x ...`    to `example ...`,
* `instance x ...` to `example ...`,
*  everything else goes to itself.

This avoids producing two declarations with the same name in the environment.
-/
def toExample {m : Type → Type} [Monad m] [MonadQuotation m] : Syntax → m Syntax
  | `($_dm:declModifiers theorem $_did:declId $ds* : $t $dv:declVal) =>
    `(example $ds* : $t $dv:declVal)
  | `($_dm:declModifiers lemma $_did:declId $ds* : $t $dv:declVal) =>
    `(example $ds* : $t $dv:declVal)
  | `($_dm:declModifiers instance $_did:declId $ds* : $t $dv:declVal) =>
    `(example $ds* : $t $dv:declVal)
  | s => return s

/-- extracts the `Array` of subsyntax of the input `Syntax` that satisfies the given predicate
`Syntax → Bool`.
-/
partial
def _root_.Lean.Syntax.findAll : Syntax → (Syntax → Bool) → Array Syntax
  | stx@(.node _ _ args), f =>
    let rest := (args.map (·.findAll f)).flatten
    if f stx then rest.push stx else rest
  | s, f => if f s then #[s] else #[]

/-- extracts "holes" `_` from the input syntax.
Converting `refine'` to `refine`, these are the candidate nodes for the replacement `_` to `?_`.
-/
def getHoles (stx : Syntax) : Array Syntax :=
  stx.findAll (·.isOfKind ``Lean.Parser.Term.hole)

/-
|-node Lean.Parser.Term.syntheticHole, none
|   |-atom original: ⟨⟩⟨⟩-- '?'
|   |-node Lean.Parser.Term.hole, none
|   |   |-atom original: ⟨⟩⟨ ⟩-- '_'

|-node Lean.Parser.Term.hole, none
|   |-atom original: ⟨⟩⟨⟩-- '_'
-/

/-- converts an "anonymous hole" `_` to a "synthetic hole" `?_` with comparable
`SourceInfo`.
Leaves unchanged inputs that are not "anonymous holes".
-/
def holeToSyntHole : Syntax → Syntax
  | hole@(.node si ``Lean.Parser.Term.hole _) =>
    .node si ``Lean.Parser.Term.syntheticHole #[mkAtomFrom hole "?", hole]
  | s => s

/-- extracts `refine'` from the input syntax. -/
def getRefine's (stx : Syntax) : Array Syntax :=
  stx.findAll (·.isOfKind ``Lean.Parser.Tactic.refine')

/-- `candidateRefines stx` returns the array `#[stx₁, ..., stxₙ]`, where each `stxᵢ` is obtained
from `stx` by replacing a subset of the `_` with `?_`.

The intended application is when `stx` is a syntax node representing `refine' ...`. -/
def candidateRefines (stx : Syntax) : Array Syntax := Id.run do
  let mut cands := #[]
  let holes := getHoles stx
  for sub in holes.toList.sublistsFast do
    let mut newCmd := stx
    for s in sub do
      newCmd ← newCmd.replaceM (fun t =>
        if t == s && t.getPos? == s.getPos? then some (holeToSyntHole s) else none)
    --let ncmd ← stx.replaceM (fun s => if sub.contains s then )
    cands := cands.push newCmd
  return cands

--/-- extracts `refine'` from the given `Syntax`, returning also the `SourceInfo`, the arguments
--of the `refine'` node and whether `refine'` contains `..`. -/
--partial
--def refine'ToRefines : Syntax → Array Syntax
--  | stx@(.node si ``Lean.Parser.Tactic.refine' args) =>
--    dbg_trace "refine' found"
--    let rest := (args.map getRefine').flatten
--    rest.push (stx, si, args, stx.find? (·.isOfKind ``Lean.Parser.Term.optEllipsis))
--  | .node _ _ args => (args.map getRefine').flatten
--  | _ => default

def refine'ToRefine (stx : Syntax) : Syntax := Id.run do
  stx.replaceM (fun s => match s with
    | .node si ``Lean.Parser.Tactic.refine' args =>
      let args := args.modify 0 fun _ => mkAtomFrom args[0]! "refine"
      return some (.node si ``Lean.Parser.Tactic.refine args)
    | _ => return none)


elab "ho " cmd:command : command => do
  let noDashCmd := refine'ToRefine cmd
  logInfo noDashCmd
  let s ← get
  --let holes := getHoles noDashCmd
  --let sholes := holes.map (holeToSyntHole ·)
  --logInfo m!"{holes}, {holes.map (·.getPos?)}, {sholes}, {sholes.map (·.getPos?)}"
  let cands := candidateRefines noDashCmd
  logInfo m!"{cands}"
  let mut opts := #[]
  for cand in cands do
    Command.elabCommand cand
    if !(← get).messages.hasErrors then opts := opts.push cand
    set s
  logInfo m!"{opts}"
  logInfo m!"{opts.map fun s => let hs := getHoles s; hs.map (·.getPos?)}"
  Command.elabCommand cmd

/-- replaces each `refine'` by `refine` in succession in `cmd` and, each time, catches the errors
of missing `?`, collecting their positions.  Eventually, it returns an array of pairs
`(1/0, position)`, where
* `1` means that the `position` is the beginning of `refine'` and
* `0` means that the `position` is a missing `?`.
-/
def getQuestions' (cmd : Syntax) :
    Command.CommandElabM (List (Nat × String.Pos)) := do
  let exm ← toExample cmd
  let st ← get
  --let origMsgsSize := s.messages.msgs.toArray.size
  --let mut mms := #[]
  --dbg_trace origMsgsSize
  let refine's := getRefine's cmd
  --logInfo m!"{refine's}"
  let mut opts := #[]
  let mut refs := #[]
  for refine' in refine's do
    --let mut current := #[]
    let refine := refine'ToRefine refine'
    let cands := candidateRefines refine
    for cand in cands do
      let repl ← exm.replaceM fun s => if s == refine' then return some cand else return none
      Command.elabCommand repl
      --mms := mms.push (repl, ← (← get).messages.msgs.toArray.mapM (·.toString))
      --dbg_trace (← get).messages.msgs.toArray.size
      if !(← get).messages.hasErrors then
        opts := opts.push cand
        refs := refs.push refine'.getPos?
        --current := current.push (0, cand.getPos?)
      set st
    --newOpts := newOpts.push ((1, refine'.getPos?), current)

    --logInfo m!"{newOpts}"
--    logInfo m!"{refine'.getPos?}"
  let positions := opts.map fun s => let hs := getHoles s; hs.map (·.getPos?)
--  let newPositions := newOpts.map fun (n, s) =>
--    let hs := getHoles s
--    hs.map fun h : Syntax => (n, h.getPos?)
--  --logInfo m!"{mms}"
  logInfo m!"{opts.zip positions}"
  return (refs.zipWith positions fun a b =>
    #[(1, a.getD default)] ++ (b.map (0, ·.getD default))).flatten.toList

/-- checks whether a `MessageData` refers to an error of a missing `?` is `refine`. -/
def isSyntPlaceHolder : MessageData → Bool
  | .withNamingContext _ (.withContext _ (.tagged `Elab.synthPlaceholder _)) => true
  | _ => false

/-- extracts `refine'` from the given `Syntax`, returning also the `SourceInfo`, the arguments
of the `refine'` node and whether `refine'` contains `..`. -/
partial
def getRefine' : Syntax → Array (Syntax × SourceInfo × Array Syntax × Option Syntax)
  | stx@(.node si ``Lean.Parser.Tactic.refine' args) =>
    --dbg_trace "refine' found"
    let rest := (args.map getRefine').flatten
    rest.push (stx, si, args, stx.find? (·.isOfKind ``Lean.Parser.Term.optEllipsis))
  | .node _ _ args => (args.map getRefine').flatten
  | _ => default

/-- replaces each `refine'` by `refine` in succession in `cmd` and, each time, catches the errors
of missing `?`, collecting their positions.  Eventually, it returns an array of pairs
`(1/0, position)`, where
* `1` means that the `position` is the beginning of `refine'` and
* `0` means that the `position` is a missing `?`.
-/
def getQuestions (cmd : Syntax) : Command.CommandElabM (Array (Nat × Position)) := do
  let s ← get
  let fm ← getFileMap
  let refine's := getRefine' cmd
  let newCmds := refine's.map fun (r, si, args, dots?) => Id.run do
      if let some dots := dots? then dbg_trace "{dots} present"
      let ncm ← cmd.replaceM fun s => if s == r then
        let args := args.modify 0 fun _ => mkAtomFrom args[0]! "refine "
        return some (.node si ``Lean.Parser.Tactic.refine args)
        else return none
      return (r, ncm)
  let mut poss := #[]
  for (r, ncmd) in newCmds do
    let exm ← toExample ncmd
    Elab.Command.elabCommand exm
    let msgs := (← get).messages.msgs
    --dbg_trace msgs.toArray.map (·.endPos)
    let ph := msgs.filter (fun m => isSyntPlaceHolder m.data)
    if ! ph.toArray.isEmpty then
      -- a repetition in `Position`s is an indication that `refine` cannot replace `refine'`
      let positions := (ph.map (·.pos)).toList
      if positions == positions.eraseDup then
        --dbg_trace ph.size == msgs.size
        --dbg_trace ph.toArray.map (·.endPos)
        poss := poss ++
          (ph.map (0, ·.pos)).toArray.push (1, fm.toPosition (r.getPos?.getD default))
  set s
  return poss

/-- Gets the value of the `linter.refine'ToRefine` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.refine'ToRefine o

/-- Reports the positions of missing `?`. -/
def refine'ToRefineLinter : Linter where run stx := do
  if getLinterHash (← getOptions) then
    let pos ← getQuestions' stx
    if ! pos.isEmpty then logInfo m!"{pos}" --else logInfo "fail"

initialize addLinter refine'ToRefineLinter
