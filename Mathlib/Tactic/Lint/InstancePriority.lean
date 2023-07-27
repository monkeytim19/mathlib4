import Mathlib

open Lean Meta Elab Command

-- generalized, but reversed the order of the arrows!
/-- Write an import graph, represented as a an array of `NameMap`s to the ".dot" graph format.
  If `("style1", graph1)` is in `graphs`, then the edges in `graph1` will be labeled with `[style1]`.
  Example: `asStyledDotGraph #[("", graph1), ("style=dashed", graph2)]` -/
def asStyledDotGraph [ForIn Id α Name] (graphs : Array (String × NameMap α))
    (header := "import_graph") : String := Id.run do
  let mut lines := #[s!"digraph \"{header}\" " ++ "{"]
  for (style, graph) in graphs do
    let label := if style == "" then "" else s!" [{style}]"
    for (n, is) in graph do
      for i in is do
        lines := lines.push s!"  \"{n}\" -> \"{i}\"{label};"
  lines := lines.push "}"
  return "\n".intercalate lines.toList

/-- Write an import graph, represented as a a `NameMap` to the ".dot" graph format. -/
def asDotGraph [ForIn Id α Name] (graph : NameMap α) (header := "import_graph") : String :=
  asStyledDotGraph #[("", graph)] header

-- slightly modified from elsewhere
private def isBlackListed (declName : Name) : CoreM Bool := do
  if declName.getRoot == `Lean then return true
  let env ← getEnv
  pure $ declName.isInternal'
   || isAuxRecursor env declName
   || isNoConfusion env declName
  <||> isRec declName <||> isMatcher declName

namespace Lean

instance (α : Type u) (cmp : α → α → Ordering) : Singleton α (RBTree α cmp) where
  singleton x := .insert ∅ x

instance : Singleton Name NameSet where
  singleton x := .insert ∅ x

instance (α : Type u) (cmp : α → α → Ordering) : Insert α (RBTree α cmp) where
  insert x xs := xs.insert x

instance : Insert Name NameSet where
  insert x xs := xs.insert x

/-- Given `t : RBMap α β` where the value type `β` implements `Singleton γ β` and `Insert γ β`
instances.
For example, `β = List γ` or `β = RBTree γ`. Then `t.insert2 x (y : γ)` inserts `y` at key `x` into
`t`. -/
def RBMap.insert2 [Singleton γ β] [Insert γ β] {cmp : α → α → Ordering} (t : RBMap α β cmp)
    (x : α) (y : γ) : RBMap α β cmp :=
  match t.find? x with
  | some ys => t.insert x (Insert.insert y ys)
  | none    => t.insert x {y}

/-- `RBMap.insert2` specialized to `NameMap`. -/
def NameMap.insert2 [Singleton γ β] [Insert γ β] (t : NameMap β)
    (x : Name) (y : γ) : NameMap β :=
  RBMap.insert2 t x y

/-- descendants of `x`, excluding `x`. -/
def NameMap.descendants (g : NameMap NameSet) (x : Name) (fuel := 10000) : NameSet :=
  go fuel [x] {}
where
  go : ℕ → List Name → NameSet → NameSet
  | 0,      _,     results => results
  | _,      [],    results => results
  | fuel+1, x::xs, results =>
    match g.find? x with
    | some nms => Id.run do
      let mut todo := xs
      let mut found := results
      for nm in nms do
        if !results.contains nm then
          todo := nm::todo
          found := found.insert nm
      go fuel todo found
    | none => go fuel xs results

/-- if s is downwards closed, find maximal elements in s. -/
def NameMap.maximals (g : NameMap NameSet) (s : NameSet) : NameSet := Id.run do
  let mut maximal : NameSet := {}
  let mut notMaximal : NameSet := {}
  for x in s do
    match g.find? x with
    | some nms => notMaximal := notMaximal ++ nms
    | none => ()
  for x in s do
    if !notMaximal.contains x then
      maximal := maximal.insert x
  return maximal

def NameMap.commonDescendants (g : NameMap NameSet) (x y : Name) : NameSet := Id.run do
  let xs := g.descendants x
  let ys := g.descendants y
  let mut common : NameSet := {}
  for nm in xs do
    if ys.contains nm then
      common := common.insert nm
  common

def NameMap.maximalCommonDescendants (g : NameMap NameSet) (x y : Name) : NameSet :=
  g.maximals <| g.commonDescendants x y

def structureIsCoherent

/-- Turn a file name into a path, relative from the root of the appropriate project.
Assumes `/` as directory seprator. -/
def Name.toPath (module : Name) : String :=
  go module ++ ".lean"
where
  go : Name → String
  | .anonymous => ""
  | .str .anonymous s => s
  | .num .anonymous n => toString n
  | .str nm s => go nm ++ "/" ++ s
  | .num nm n => go nm ++ "/" ++ toString n

end Lean

/-- this instance causes a cycle -/
def blacklisted : NameSet :=
  .ofList [`CategoryTheory.locallySmall_self]

/--
Retrieve all names in the environment satisfying a predicate as a NameSet.
-/
def allNamesAsSet (p : Name → Bool) : CoreM NameSet := do
  (← getEnv).constants.foldM (init := {}) fun names n _ => do
    if p n && !(← isBlackListed n) then
      return names.insert n
    else
      return names

def getClassInstanceGraph (full := true) : MetaM (NameMap NameSet) := do
  let env ← getEnv
  let classes := classExtension.getState env |>.outParamMap.toList.map (·.1)
  let classes : List (Name × List Name) ← classes.filterMapM fun nm => do
    forallTelescope (← inferType (← mkConstWithLevelParams nm)) fun args _ => do
      unless args.size ≥ 1 do return none
      unless full || args.size == 1 do return none
      let ldecls ← args.mapM (·.fvarId!.getDecl)
      let bis := ldecls.map (·.binderInfo)
      unless (bis.toList.drop 1).all (· == .instImplicit) &&
        (← whnf ldecls[0]!.type).isSort do return none
      let tgts := ldecls.toList.drop 1 |>.map (·.type.getAppFnArgs.1)
      return some (nm, tgts)
  let argumentGraph : NameMap NameSet := classes.foldl (init := {}) fun r (src, tgts) =>
    r.insert src <| .ofList tgts
  let classSet : NameSet := .ofList <| classes.map (·.1)
  let rawInstances := instanceExtension.getState env |>.instanceNames.toList.map (·.1)
  let instances : List (Name × List Name × Name) ← rawInstances.filterMapM fun nm => do
    forallTelescope (← inferType (← mkConstWithLevelParams nm)) fun args ty => do
      unless args.size ≥ 2 do return none
      unless full || args.size == 2 do return none
      let typeVar := args[0]!
      let (targetClass, targetClassArgs) := ty.getAppFnArgs
      unless classSet.contains targetClass do return none
      unless targetClassArgs[0]? == some typeVar do return none
      if blacklisted.contains nm then return none
      let mut srcs := []
      let mut dupes : NameSet := {}
      for arg in args.toList.drop 1 do
        let (sourceClass, sourceClassArgs) := (← inferType arg).getAppFnArgs
        unless classSet.contains sourceClass do return none
        unless sourceClassArgs[0]? == some typeVar do return none
        srcs := sourceClass::srcs
        dupes := dupes ++ (argumentGraph.find? sourceClass).get!
      let sources := srcs.filter (!dupes.contains ·)
      return (nm, sources, targetClass)
  let instanceSet : NameSet := .ofList <| instances.map (·.1)
  let instances2 : List (Name × Name) ← rawInstances.filterMapM fun nm => do
    forallTelescope (← inferType (← mkConstWithLevelParams nm)) fun args ty => do
      unless args.size ≥ 1 do return none
      if instanceSet.contains nm then return none
      let prio := (← getInstancePriority? nm).get!
      if prio < 1000 then return none
      let (targetClass, targetClassArgs) := ty.getAppFnArgs
      let outParams := getOutParamPositions? env targetClass
      let relevantArgs : Array (Option Expr) ←
        forallTelescope (← inferType (← mkConstWithLevelParams targetClass)) fun clArgs _ => do
          let bis ← clArgs.mapM (·.fvarId!.getBinderInfo)
          if bis.size != targetClassArgs.size then logInfo m!"{nm}"; return #[]
          return (targetClassArgs.zip bis).mapIdx fun i (e, bi) =>
            if outParams.isSome && outParams.get!.contains (i : ℕ) then none else
              if bi == BinderInfo.instImplicit then none else some e
      let relevantArgs := relevantArgs.reduceOption
      if relevantArgs.any (!·.isFVar) then return none
      let relevantArgs := relevantArgs.toList.map (·.fvarId!.name)
      if !relevantArgs.Nodup then return none
      let lastArg ← args[args.size - 1]!.fvarId!.getDecl
      unless lastArg.binderInfo == .instImplicit do return none
      let (sourceClass, _) := lastArg.type.getAppFnArgs
      if sourceClass == .anonymous then do return none
      return some (nm, sourceClass)

  let instanceGraph : NameMap NameSet := instances.foldl (init := {}) fun r (_, src, tgt) =>
    if src.length == 1 then r.insert2 src.head! tgt else r
  let realParents : NameSet := .ofList <| .join <| classes.map fun (cl, _) => Id.run do
    unless isStructure env cl do return [] -- filter class inductives
    let fields := getStructureFields env cl |>.toList
    let fields := fields.filter fun nm => isSubobjectField? env cl nm |>.isSome
    let fields := fields.map (cl ++ ·)
    return fields
  -- let prios ← instances.filterMapM fun (inst, src, _) => do
  --   let prio := (← getInstancePriority? inst).get!
  --   if prio < 1000 then return none
  --   let newPrio := if realParents.contains inst then 200 else 180
  --   let src := src[0]!
  --   let file := (env.getModuleFor? src).get!.toPath
  --   unless file.startsWith "Mathlib" do return none
  --   return some s!"sed -i -E 'H;1h;$!d;x; s/(class {src}([^\\n]|\\n[^\\n])*\\n)\\n/\\1attribute [instance {newPrio}] {inst}\\n\\n/g' {file}\n"
  -- let cmds : String := prios.foldl (· ++ ·) ""
  -- let prios2 ← instances2.filterMapM fun (inst, src) => do
  --   let newPrio := 200
  --   let file := (env.getModuleFor? src).get!.toPath
  --   unless file.startsWith "Mathlib" do return none
  --   return some s!"sed -i -E 'H;1h;$!d;x; s/(\\nclass {src}([^\\n]|\\n[^\\n])*\\n)\\n/\\1attribute [instance {newPrio}] {inst}\\n\\n/g' {file}\n"
  -- let cmds2 : String := prios2.foldl (· ++ ·) ""
  -- logInfo m!"{realParents.toList}"
  --find . -type f -print0 | xargs -0 sed -i -E 'H;1h;$!d;x; s/(class NonemptyFinLinOrd(.|\n.)*\n)\n/\1test\n\n/g' test.txt
  -- logInfo m!"{instances2}"
  -- logInfo m!"{cmds}"
  -- logInfo m!"{cmds2}"
  -- logInfo m!"{prios}"
  logInfo m!"{instanceGraph.descendants `Group |>.toList}"
  logInfo m!"{instanceGraph.commonDescendants `AddCommGroup `NonUnitalNonAssocSemiring |>.toList}"
  logInfo m!"{instanceGraph.maximalCommonDescendants `AddCommMonoid `MulZeroClass |>.toList}"
  logInfo m!"{instanceGraph.maximalCommonDescendants `MulZeroClass `Distrib |>.toList}"

  logInfo m!"classes with 1 type parameter: {classSet.size}"
  logInfo m!"instances between these classes: {instances.length}"
  -- logInfo m!"classes: {classes}"
  logInfo m!"forgetful instances with 1 source class: {instanceGraph.size}"
  logInfo m!"argument instances: {argumentGraph.size}"
  -- logInfo m!"instances: {instances}"
  -- logInfo m!"{asStyledDotGraph #[("", instanceGraph), ("style=dashed", argumentGraph)] "instance_graph"}"
  -- logInfo m!"instances with more than 1 source: {instances.filter (·.2.1.length > 1)}"
  return instanceGraph
  -- return .empty

set_option profiler true
run_cmd liftCoreM <| MetaM.run' <| do
  getClassInstanceGraph

-- set_option maxHeartbeats 0 in
-- #find List String -> String

-- /-!
-- Instance priority linter
-- -/

-- namespace Std.Tactic.Lint
-- open Lean Meta

-- /--
-- Lints for extends with wrong instance priorities
-- -/
-- @[std_linter] def priorityInstance : Linter where
--   noErrorsFound := "no incoherent instance priority instances found."
--   errorsFound := "SOME INSTANCES HAVE INCOHERENT INSTANCE PRIORITY.
-- Either increase these instance priorities, or reorder the `extends` arguments to the structure."
--   test declName := do
--     unless isClass (← getEnv) declName do return none
--     forallTelescopeReducing (← inferType (← mkConstWithLevelParams declName)) fun args ty => do
--     let argTys ← args.mapM inferType
--     let impossibleArgs ← args.zipWithIndex.filterMapM fun (arg, i) => do
--       let fv := arg.fvarId!
--       if (← fv.getDecl).binderInfo.isInstImplicit then return none
--       if ty.containsFVar fv then return none
--       if argTys[i+1:].any (·.containsFVar fv) then return none
--       return some m!"argument {i+1} {arg} : {← inferType arg}"
--     if impossibleArgs.isEmpty then return none
--     addMessageContextFull <| .joinSep impossibleArgs.toList ", "
